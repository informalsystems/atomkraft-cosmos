----------------------------- MODULE AuthzService ------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS Grants, Maps, Integers

\* grantStore represents the KV store implemented by the authz module in the
\* server, used to store mappings from grant triples to authorizations.
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
(* Request grant                                                              *)
(******************************************************************************)

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L14
\* @type: (MSG_GRANT) => RESPONSE_GRANT;
CallGrant(msgGrant) == 
    IF msgGrant.granter = msgGrant.grantee THEN 
        [type |-> "response-grant", ok |-> FALSE, error |-> "granter-equal-grantee"]
    ELSE IF msgGrant.grant.expiration = "past" THEN 
        [type |-> "response-grant", ok |-> FALSE, error |-> "authorization-expired"]
    ELSE 
        [type |-> "response-grant", ok |-> TRUE, error |-> "none"]

--------------------------------------------------------------------------------
(******************************************************************************)
(* Request revoke                                                             *)
(******************************************************************************)

\* @type: (MSG_REVOKE) => GRANT_ID;
grantIdOfMsgRevoke(msg) == [
    grantee |-> msg.grantee,
    granter |-> msg.granter,
    msgTypeUrl |-> msg.msgTypeUrl
]

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L52
\* @type: (MSG_REVOKE) => RESPONSE_REVOKE;
CallRevoke(msgRevoke) == 
    IF ~ HasGrant(grantIdOfMsgRevoke(msgRevoke)) THEN
        [type |-> "response-revoke", ok |-> FALSE, error |-> "grant-not-found"]
    ELSE
        [type |-> "response-revoke", ok |-> TRUE, error |-> "none"]

--------------------------------------------------------------------------------
(******************************************************************************)
(* Request execute                                                            *)
(******************************************************************************)

NoUpdate == [type |-> "no-update"]

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/keeper.go#L90
\* @typeAlias: ACCEPT_RESPONSE = [accept: Bool, delete: Bool, updated: AUTH, error: Str];
\* @type: (ACCOUNT, SDK_MSG) => ACCEPT_RESPONSE;
DispatchActionsOneMsg(grantee, msg) == 
    LET 
        granter == msg.signer \* An SDK message may contain multiple signers; but authz accepts messages with just one.
        grantId == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msg.typeUrl]
    IN
    
    \* In the code, it is said that if granter = grantee "we implicitly accept"
    \* the message. But then the execution of the message fails because there
    \* should not exist any grant with granter = grantee.
    IF granter = grantee \/ ~ HasGrant(grantId) THEN 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "grant-not-found"]
    ELSE IF grantStore[grantId].expiration = "past" THEN 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "authorization-expired"]
    ELSE 
        Accept(grantStore[grantId].authorization, msg)

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L72
\* @type: (MSG_EXEC) => <<RESPONSE_EXEC, ACCEPT_RESPONSE>>;
CallExec(msgExec) == 
    LET 
        acceptResponse == DispatchActionsOneMsg(msgExec.grantee, msgExec.msg)
        execResponse == [
            type |-> "response-execute", 
            ok |-> acceptResponse.accept, 
            error |-> acceptResponse.error
        ] 
    IN 
    <<execResponse, acceptResponse>>

================================================================================
Created by Hernán Vanzetto on 10 August 2022
