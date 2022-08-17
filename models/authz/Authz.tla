-------------------------------- MODULE Authz ----------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS AuthzBase, AuthzGrants

\* The following declarations of constants should be the preferred way of
\* structuring the module. Then, for the different authorization logics, one could
\* create a separate module that instantiate Authz with their own definitions of
\* the constants. However, Apalache's parser does not accept the constant
\* Accept(_,_), though its not clearly specified in the documentation 
\* https://apalache.informal.systems/docs/apalache/features.html.

\* \* The following constants are specific to each authorization logic.
\* CONSTANTS
\*     \* Abstract interface to an Authorization.
\*     \* @type: Set(AUTH);
\*     Authorization,

\*     \* Types of messages allowed to be granted permission.
\*     \* @type: Set(MSG_TYPE_URL);
\*     MsgTypeUrls,

\*     \* @type: (GRANT_ID, SDK_MDG) => ACCEPT_RESPONSE;
\*     Accept(_,_),

\*     \* Given an authorization returns the message type URL it handles.
\*     \* @type: (AUTH) => MSG_TYPE_URL;
\*     MsgTypeURL(_),
    
\*     \* @ type: MSG_TYPE_URL;
\*     \* MsgTypeURL,

\*     \* The content of the messages to be executed.
\*     \* A set of, for example, Send messages or Stake messages
\*     \* @type: Set(Str);
\*     SdkMsgContent

--------------------------------------------------------------------------------
VARIABLES
    \* @type: GRANT_ID -> GRANT;  
    grantStore, \* Representation of the KV store implemented by the authz 
                \* module in the server, used to store mappings from grant 
                \* triples to authorizations.
    
    \* @type: REQUEST_MSG;
    lastRequest,

    \* @type: RESPONSE_MSG;
    lastResponse,

    \* @type: EVENT;
    lastEvent

-------------------------------------------------------------------------------
\* @type: (GRANT_ID) => Bool;
HasGrant(g) == g \in DOMAIN grantStore

\* @type: (GRANT_ID) => Bool;
IsExpired(g) == 
    /\ HasGrant(g)
    /\ grantStore[g].expirationTime = "past"

-------------------------------------------------------------------------------
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

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L52
CallRevoke(msgRevoke) == CHOOSE response \in MsgRevokeResponses: response.ok

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

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/keeper.go#L90
\* @type: (ADDRESS, SDK_MSG) => ACCEPT_RESPONSE;
DispatchActionsOneMsg(grantee, msg) == 
    LET 
        granter == msg.signer \* Actually, granter is the first of the list of signers.
        grantId == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msg.msgTypeUrl]
    IN
    IF granter = grantee THEN 
        [accept |-> TRUE, delete |-> FALSE, updated |-> NoUpdate, error |-> "none"]
    ELSE IF ~ HasGrant(grantId) THEN 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "grant-not-found"]
    ELSE IF grantStore[grantId].expirationTime = "past" THEN 
        [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "authorization-expired"]
    ELSE 
        Accept(grantStore[grantId].authorization, msg)

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L72
\* @type: (MSG_EXEC) => <<RESPONSE_EXEC, ACCEPT_RESPONSE>>;
CallExec(msgExec) == 
    LET msg == CHOOSE m \in msgExec.msgs: TRUE IN
    LET acceptResponse == DispatchActionsOneMsg(msgExec.grantee, msg) IN 
    LET execResponse == [
        type |-> "exec", 
        ok |-> acceptResponse.accept, 
        error |-> acceptResponse.error
    ] IN 
    <<execResponse, acceptResponse>>

-------------------------------------------------------------------------------
\* Only for the initial state.
NoRequest == [type |-> "NoRequest"]
NoResponse == [type |-> "NoResponse"]
NoEvent == [type |-> "NoEvent"]

\* EmptyMap is not accepted by Apalache's typechecker.
\* @type: GRANT_ID -> GRANT;
EmptyStore == [x \in {} |-> NoGrant]

TypeOK == 
    /\ IsMap(grantStore, ValidGrantIds, Grants)
    /\ lastRequest \in RequestMessages \cup {NoRequest}
    /\ lastResponse \in Responses \cup {NoResponse}
    /\ lastEvent \in RequestMessages \cup ExpireEvents \cup {NoEvent}

Init ==
    /\ grantStore = EmptyStore
    /\ lastRequest = NoRequest
    /\ lastResponse = NoResponse
    /\ lastEvent = NoEvent

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
        /\ lastRequest' = msg
        /\ LET response == CallGrant(msg) IN
            /\ lastResponse' = response
            /\ IF response.ok THEN
                    grantStore' = MapPut(grantStore, g, grant)
                ELSE
                    UNCHANGED grantStore

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
        /\ lastRequest' = msg
        /\ LET response == CallRevoke(msg) IN
            /\ IF response.ok THEN
                    grantStore' = MapRemove(grantStore, g)
                ELSE 
                    UNCHANGED grantStore
            /\ lastResponse' = response

\* @type: (REQUEST_MSG, ACCEPT_RESPONSE) => Bool;
PostProcessExec(request, acceptResponse) == 
    LET msg == CHOOSE m \in request.msgs: TRUE IN
    LET g == [granter |-> msg.signer, grantee |-> request.grantee, msgTypeUrl |-> msg.msgTypeUrl] IN
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
    /\ lastRequest' = request
    /\ lastResponse' = responses[1]
    /\ PostProcessExec(request, responses[2])

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
    /\ UNCHANGED <<lastRequest, lastResponse>>

--------------------------------------------------------------------------------

Next == 
    \/ \E granter, grantee \in Address, grant \in Grants: 
        RequestGrant(granter, grantee, grant)
    \/ \E g \in GrantIds: 
        RequestRevoke(g.granter, g.grantee, g.msgTypeUrl)
    \/ \E g \in ValidGrantIds: 
        Expire(g)
    \* NB: We model requests execution of only one message at a time.
    \/ \E grantee \in Address, msg \in SdkMsgs: 
        RequestExec(grantee, {msg})

================================================================================
Created by Hernán Vanzetto on 10 August 2022
