----------------------------- MODULE AuthzMethods ------------------------------
(******************************************************************************)
(* Operators modeling the methods for sending request messages, as defined in *)
(* the `Msg` service in                                                       *)
(*     https://github.com/cosmos/cosmos-sdk/blob/main/proto/cosmos/authz/v1beta1/tx.proto *)
(******************************************************************************)
EXTENDS Integers, Maps, Grants, AuthzMessages

\* The variable grantStore represents the KV store implemented by the authz
\* module, used to store mappings from grant triples to authorizations.
VARIABLE
    \* @type: GRANT_ID -> GRANT;  
    grantStore  

\* @type: (GRANT_ID) => Bool;
ExistsGrantFor(grantId) == grantId \in DOMAIN grantStore

--------------------------------------------------------------------------------
(******************************************************************************)
(* Operators that model processing of request messages.                       *)
(******************************************************************************)

\* The interface that includes the three Call operations below:
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L331

--------------------------------------------------------------------------------
(******************************************************************************)
(* Send request grant                                                         *)
(******************************************************************************)

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L14
\* @type: (MSG_GRANT) => RESPONSE_GRANT;
SendMsgGrant(msg) == 
    LET grantId == grantIdOfMsgGrant(msg) IN
    CASE MsgGrantValidateBasic(msg) # "none" ->
        [type |-> "response-grant", ok |-> FALSE, error |-> MsgGrantValidateBasic(msg)]
      [] msg.grant.expiration = "past" ->
        [type |-> "response-grant", ok |-> FALSE, error |-> INVALID_EXPIRATION]
      [] OTHER ->
        [type |-> "response-grant", ok |-> TRUE, error |-> "none"]

--------------------------------------------------------------------------------
(******************************************************************************)
(* Send request revoke                                                        *)
(******************************************************************************)

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L52
\* @type: (MSG_REVOKE) => RESPONSE_REVOKE;
SendMsgRevoke(msg) == 
    LET grantId == grantIdOfMsgRevoke(msg) IN
    CASE MsgRevokeValidateBasic(msg) # "none" ->
        [type |-> "response-revoke", ok |-> FALSE, error |-> MsgRevokeValidateBasic(msg)]
      [] ~ ExistsGrantFor(grantId) ->
        [type |-> "response-revoke", ok |-> FALSE, error |-> AUTH_NOT_FOUND]
      [] OTHER ->
        [type |-> "response-revoke", ok |-> TRUE, error |-> "none"]

--------------------------------------------------------------------------------
(******************************************************************************)
(* Send request execute                                                       *)
(******************************************************************************)

NoUpdate == [type |-> "no-update"]

\* An SDK message may contain multiple signers, but authz accepts messages with just one.
\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/keeper.go#L90
\* @typeAlias: ACCEPT_RESPONSE = [accept: Bool, delete: Bool, updated: AUTH, error: Str];
\* @type: (ACCOUNT, SDK_MSG) => ACCEPT_RESPONSE;
DispatchActionsOneMsg(grantee, msg) == 
    LET 
        \* @type: ACCOUNT;
        granter == GetSigner(msg)
        \* @type: GRANT_ID;
        grantId == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msg.typeUrl]
        \* @type: AUTH;
        auth == grantStore[grantId].authorization
    IN
    CASE granter = grantee ->
        \* A comment in the code says that if granter = grantee "we implicitly
        \* accept" the message. Note that this may execute the message even when 
        \* no authorization has been granted.
        [accept |-> TRUE, delete |-> FALSE, updated |-> NoUpdate, error |-> "none"] 
      [] ~ ExistsGrantFor(grantId) ->
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> AUTH_NOT_FOUND] 
      [] ExistsGrantFor(grantId) /\ grantStore[grantId].expiration = "past" ->
        \* CHECK: This is checked in the code but it's probably unreachable: expired grants are deleted before.
        \* https://github.com/cosmos/cosmos-sdk/blob/25e7f9bee2b35f0211b0e323dd062b55bef987b7/x/authz/keeper/keeper.go#L110
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> AUTH_EXPIRED] 
      [] SdkMsgValidateBasic(msg) # "none" ->
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> SdkMsgValidateBasic(msg)] 
      [] OTHER -> 
        Accept(auth, msg)

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L72
\* @type: (MSG_EXEC) => <<RESPONSE_EXEC, ACCEPT_RESPONSE>>;
SendMsgExecute(msg) == 
    LET 
        \* @type: ACCEPT_RESPONSE;
        acceptResponse == DispatchActionsOneMsg(msg.grantee, msg.msg)
    IN
    IF acceptResponse.accept /\ msg.msg.typeUrl \in {UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL} THEN
        \* Even if an undelegate or redelegate message is accepted, execution
        \* will fail because there are no delegations to un/redelegate. If we want
        \* to properly handle these cases, we need to keep track of delegations in
        \* the model.
        <<[type |-> "response-execute", ok |-> FALSE, error |-> FAILED_TO_EXECUTE], 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> FAILED_TO_EXECUTE]>>
    ELSE 
        <<[type |-> "response-execute", ok |-> acceptResponse.accept, error |-> acceptResponse.error], 
        acceptResponse>>

================================================================================
Created by Hernán Vanzetto on 10 August 2022
