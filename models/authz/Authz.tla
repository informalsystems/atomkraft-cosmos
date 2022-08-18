-------------------------------- MODULE Authz ----------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS AuthzGrants, Maps, Integers

VARIABLES
    \* @type: GRANT_ID -> GRANT;  
    grantStore, \* Representation of the KV store implemented by the authz 
                \* module in the server, used to store mappings from grant 
                \* triples to authorizations.
    
    \* @type: EVENT;
    lastEvent,

    \* @type: RESPONSE_MSG;
    lastResponse,

    \* @type: Int;
    numRequests

-------------------------------------------------------------------------------
\* @type: (GRANT_ID) => Bool;
HasGrant(g) == g \in DOMAIN grantStore

\* @type: (GRANT_ID) => Bool;
IsExpired(g) == 
    /\ HasGrant(g)
    /\ grantStore[g].expirationTime = "past"

--------------------------------------------------------------------------------
MsgTypeURL(auth) ==
    CASE auth.authorizationType \in Generic!MsgTypeUrls -> Generic!MsgTypeURL(auth)
      [] auth.authorizationType \in Send!MsgTypeUrls -> Send!MsgTypeURL(auth)
      [] auth.authorizationType \in Stake!MsgTypeUrls -> Stake!MsgTypeURL(auth)

Accept(auth, msg) ==
    CASE msg.typeUrl \in Generic!MsgTypeUrls -> 
        Generic!Accept(auth, msg)
      [] msg.typeUrl \in Send!MsgTypeUrls -> 
        Send!Accept(auth, msg)
      [] msg.typeUrl \in Stake!MsgTypeUrls -> 
        Stake!Accept(auth, msg)

--------------------------------------------------------------------------------
AcceptErrors == {
    "none", 
    "validator-not-allowed",
    "validator-denied",
    "insufficient-amount"
}

NoUpdate == [type |-> "NoUpdate"]

(* AcceptResponse instruments the controller of an authz message if the request
is accepted and if it should be updated or deleted. *)
\* https://github.com/cosmos/cosmos-sdk/blob/f2cea6a137ce19ad8987fa8a0cb99f4b37c4484d/x/authz/authorizations.go#L20
\* @typeAlias: ACCEPT_RESPONSE = [accept: Bool, delete: Bool, updated: AUTH, error: Str];
\* @type: Set(ACCEPT_RESPONSE);
AcceptResponse == [
	\* If Accept=true, the controller can accept and authorization and handle the update.
	accept: BOOLEAN,
	
    \* If Delete=true, the controller must delete the authorization object and release storage resources.
	delete: BOOLEAN,
	
    \* Controller, who is calling Authorization.Accept must check if `Updated !=
    \* nil`. If yes, it must use the updated version and handle the update on the
    \* storage level.
    updated: Authorization \cup {NoUpdate},

    \* This field does not appear in the code; it's here just to simplify the spec.
    error: AcceptErrors
]

--------------------------------------------------------------------------------
(******************************************************************************)
(* Operators that model processing of request messages. *)
(******************************************************************************)

\* The interface that includes the three operations below:
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L331

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L14
\* @type: (MSG_GRANT) => RESPONSE_GRANT;
CallGrant(msgGrant) == 
    IF msgGrant.granter = msgGrant.grantee THEN 
        [type |-> "grant", ok |-> FALSE, error |-> "granter-equal-grantee"]
    ELSE IF msgGrant.grant.expirationTime = "past" THEN 
        [type |-> "grant", ok |-> FALSE, error |-> "authorization-expired"]
    ELSE 
        [type |-> "grant", ok |-> TRUE, error |-> "none"]

--------------------------------------------------------------------------------
\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L52
CallRevoke(msgRevoke) == CHOOSE response \in MsgRevokeResponses: response.ok

--------------------------------------------------------------------------------
\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/keeper.go#L90
\* @type: (ADDRESS, SDK_MSG) => ACCEPT_RESPONSE;
DispatchActionsOneMsg(grantee, msg) == 
    LET 
        granter == msg.signer \* Actually, granter is the first of the list of signers.
        grantId == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msg.content.typeUrl]
    IN
    IF granter = grantee THEN 
        [accept |-> TRUE, delete |-> FALSE, updated |-> NoUpdate, error |-> "none"]
    ELSE IF ~ HasGrant(grantId) THEN 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "grant-not-found"]
    ELSE IF grantStore[grantId].expirationTime = "past" THEN 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "authorization-expired"]
    ELSE 
        Accept(grantStore[grantId].authorization, msg.content)

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L72
\* @type: (MSG_EXEC) => <<RESPONSE_EXEC, ACCEPT_RESPONSE>>;
CallExec(msgExec) == 
    LET 
        \* NB: We model requests execution of only one message per call.
        msg == CHOOSE m \in msgExec.msgs: TRUE 
        acceptResponse == DispatchActionsOneMsg(msgExec.grantee, msg)
        execResponse == [
            type |-> "exec", 
            ok |-> acceptResponse.accept, 
            error |-> acceptResponse.error
        ] 
    IN 
    <<execResponse, acceptResponse>>

-------------------------------------------------------------------------------
\* Only for the initial state.
NoResponse == [type |-> "NoResponse"]
NoEvent == [type |-> "NoEvent"]

\* EmptyMap is not accepted by Apalache's typechecker.
\* @type: GRANT_ID -> GRANT;
EmptyStore == [x \in {} |-> NoGrant]

TypeOK == 
    /\ IsMap(grantStore, ValidGrantIds, Grants \cup {NoGrant})
    /\ lastEvent \in RequestMessages \cup ExpireEvents \cup {NoEvent}
    /\ lastResponse \in Responses \cup {NoResponse}
    /\ numRequests \in Nat

Init ==
    /\ grantStore = EmptyStore
    /\ lastEvent = NoEvent
    /\ lastResponse = NoResponse
    /\ numRequests = 0

(*****************************************************************************)
(* An authorization grant is created using the MsgGrant message. If there is
already a grant for the (granter, grantee, Authorization) triple, then the new
grant overwrites the previous one. To update or extend an existing grant, a new
grant with the same (granter, grantee, Authorization) triple should be created.

The message handling should fail if:
- both granter and grantee have the same address.
- provided Expiration time is less than current unix timestamp.
- provided Grant.Authorization is not implemented.
- Authorization.MsgTypeURL() is not defined in the router (there is no defined
handler in the app router to handle that Msg types). *)
(*****************************************************************************)

\* @type: (ADDRESS, ADDRESS, GRANT) => Bool;
RequestGrant(granter, grantee, grant) ==
    LET 
        msgTypeUrl == MsgTypeURL(grant.authorization)
        g == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msgTypeUrl]
    IN
    /\ IsValid(g)
    /\ ~ HasGrant(g) \/ IsExpired(g)
    /\ LET msg == [type |-> "grant", granter |-> granter, grantee |-> grantee, grant |-> grant] IN
        /\ lastEvent' = msg
        /\ LET response == CallGrant(msg) IN
            /\ lastResponse' = response
            /\ IF response.ok THEN
                    grantStore' = MapPut(grantStore, g, grant)
                ELSE
                    UNCHANGED grantStore
    /\ numRequests' = numRequests + 1

(*****************************************************************************)
(* Request to revoke an existing active grant. *)
(*****************************************************************************)
\* @type: (ADDRESS, ADDRESS, MSG_TYPE_URL) => Bool;
RequestRevoke(granter, grantee, msgTypeUrl) == 
    LET g == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msgTypeUrl] IN
    /\ IsValid(g)
    /\ HasGrant(g)
    /\ LET msg == [type |-> "revoke", granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msgTypeUrl] IN
        /\ lastEvent' = msg
        /\ LET response == CallRevoke(msg) IN
            /\ IF response.ok THEN
                    grantStore' = MapRemove(grantStore, g)
                ELSE 
                    UNCHANGED grantStore
            /\ lastResponse' = response
    /\ numRequests' = numRequests + 1

\* @type: (ADDRESS, Set(SDK_MSG), ACCEPT_RESPONSE) => Bool;
PostProcessExec(grantee, msgs, acceptResponse) == 
    LET 
        \* @type: SDK_MSG;
        msg == CHOOSE m \in msgs: TRUE
        \* @type: GRANT_ID;
        g == [granter |-> msg.signer, grantee |-> grantee, msgTypeUrl |-> msg.content.typeUrl] 
    IN
    IF acceptResponse.delete THEN
        grantStore' = MapRemove(grantStore, g)
    ELSE IF acceptResponse.accept /\ acceptResponse.updated # NoUpdate THEN
        grantStore' = [grantStore EXCEPT ![g].authorization = acceptResponse.updated]
    ELSE
        UNCHANGED <<grantStore>>

(*****************************************************************************)
(* The predicate which models the execution of a message. It checks whether
there is an appropriate grant for the execution message, but does not model the
actual execution and whether or not the execution itself fails. *)
(*****************************************************************************)
\* @type: (ADDRESS, Set(SDK_MSG)) => Bool;
RequestExec(grantee, msgs) ==
    LET request == [type |-> "exec", grantee |-> grantee, msgs |-> msgs] IN
    LET responses == CallExec(request) IN
    /\ lastEvent' = request
    /\ lastResponse' = responses[1]
    /\ PostProcessExec(grantee, msgs, responses[2])
    /\ numRequests' = numRequests + 1

(*****************************************************************************)
(* Timeout being reached is abstracted away by the action Expire. What is
lost then is the relation between different grants and their expirations (in
real life, there could be a dependency: if A expires, then definitely B and C
have to expire). This action is a pure environment action and thus it does not
remove the grant from a set of active grants (the system will do so once it
notices that the grant expired, upon running the Execute function). *)
(*****************************************************************************)
Expire(g) ==
    /\ HasGrant(g)
    /\ ~ IsExpired(g)
    /\ grantStore' = [grantStore EXCEPT ![g].expirationTime = "past"]
    /\ LET event == [type |-> "expire", g |-> g] IN
        lastEvent' = event
    /\ UNCHANGED <<lastResponse, numRequests>>

--------------------------------------------------------------------------------

Next == 
    \/ \E granter, grantee \in Address, grant \in Grants: 
        RequestGrant(granter, grantee, grant)
    \/ \E g \in GrantIds: 
        RequestRevoke(g.granter, g.grantee, g.msgTypeUrl)
    \/ \E g \in ValidGrantIds: 
        Expire(g)
    \* NB: We model requests execution of only one message per call.
    \/ \E grantee \in Address, msg \in SdkMsgs: 
        RequestExec(grantee, {msg})

================================================================================
Created by Hernán Vanzetto on 10 August 2022
