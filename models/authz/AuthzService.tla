----------------------------- MODULE AuthzService ------------------------------
(******************************************************************************)
(* Operators modeling the methods for sending request messages, as defined in *)
(* the `Msg` service in                                                       *)
(*     https://github.com/cosmos/cosmos-sdk/blob/main/proto/cosmos/authz/v1beta1/tx.proto *)
(******************************************************************************)
EXTENDS Integers, MsgTypes, Maps, Grants

\* The variable grantStore represents the KV store implemented by the authz
\* module, used to store mappings from grant triples to authorizations.
VARIABLE
    \* @type: GRANT_ID -> GRANT;  
    grantStore  

\* @type: (GRANT_ID) => Bool;
HasGrant(grantId) == grantId \in DOMAIN grantStore

\* @type: (GRANT_ID) => Bool;
IsExpired(grantId) == 
    /\ HasGrant(grantId)
    /\ grantStore[grantId].expiration = "past"

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
\* @type: (MSG_GRANT) => GRANT_ID;
grantIdOfMsgGrant(msg) == [
    grantee |-> msg.grantee,
    granter |-> msg.granter,
    msgTypeUrl |-> MsgTypeURL(msg.grant.authorization)
]

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L14
\* @type: (MSG_GRANT) => RESPONSE_GRANT;
SendMsgGrant(msg) == 
    LET grantId == grantIdOfMsgGrant(msg) IN
    CASE IsValid(grantId) ->
        [type |-> "response-grant", ok |-> FALSE, error |-> GRANTER_EQUALS_GRANTEE]
      [] msg.grant.expiration = "past" ->
        [type |-> "response-grant", ok |-> FALSE, error |-> INVALID_EXPIRATION]
      [] OTHER ->
        [type |-> "response-grant", ok |-> TRUE, error |-> "none"]

--------------------------------------------------------------------------------
(******************************************************************************)
(* Send request revoke                                                        *)
(******************************************************************************)

\* @type: (MSG_REVOKE) => GRANT_ID;
grantIdOfMsgRevoke(msg) == [
    grantee |-> msg.grantee,
    granter |-> msg.granter,
    msgTypeUrl |-> msg.msgTypeUrl
]

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L52
\* @type: (MSG_REVOKE) => RESPONSE_REVOKE;
SendMsgRevoke(msg) == 
    LET grantId == grantIdOfMsgRevoke(msg) IN
    CASE IsValid(grantId) ->
        [type |-> "response-revoke", ok |-> FALSE, error |-> GRANTER_EQUALS_GRANTEE]
      [] ~ HasGrant(grantId) ->
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
        \* @type: GRANT_ID;
        grantId == [granter |-> msg.signer, grantee |-> grantee, msgTypeUrl |-> msg.typeUrl]
        \* @type: AUTH;
        auth == grantStore[grantId].authorization
    IN
    CASE IsValid(grantId) ->
        \* A comment in the code says that if granter = grantee "we implicitly
        \* accept" the message.
        [accept |-> TRUE, delete |-> FALSE, updated |-> NoUpdate, error |-> "none"]
      [] msg.typeUrl = SEND_TYPE_URL /\ grantee = msg.fromAddress -> 
        \* CHECK: This will execute the message even when no authorization has been granted.
        Accept(auth, msg)
      [] msg.typeUrl = DELEGATE_TYPE_URL /\ grantee = msg.delegatorAddress ->
        \* CHECK: This will execute the message even when no authorization has been granted.
        Accept(auth, msg)
      [] ~ IsValid(grantId) /\ IsExpired(grantId) ->
        \* CHECK: Probably unreachable: expired grants are deleted before.
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> AUTH_EXPIRED] 
      [] ~ IsValid(grantId) /\ ~ HasGrant(grantId) ->
        \* There are multiple reasons for failing to execute a message and they
        \* depend on the kind of message being executed.
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> FAILED_TO_EXECUTE] 
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
        \* Message is accepted but execution will fail because there are no delegations to un/redelegate.
        <<[type |-> "response-execute", ok |-> FALSE, error |-> FAILED_TO_EXECUTE], 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> FAILED_TO_EXECUTE]>>
    ELSE 
        <<[type |-> "response-execute", ok |-> acceptResponse.accept, error |-> acceptResponse.error], 
        acceptResponse>>

================================================================================
Created by Hernán Vanzetto on 10 August 2022
