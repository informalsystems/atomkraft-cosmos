-------------------------------- MODULE Authz ----------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS AuthzBase

\* The following constants are specific to each authorization logic.
CONSTANTS
    \* Abstract interface to an Authorization.
    \* @type: Set(AUTH);
    Authorization,

    \* Types of messages allowed to be granted permission.
    \* @type: Set(MSG_TYPE_URL);
    MsgTypeUrls,

    \* @type: (GRANT_ID, SDK_MDG) => ACCEPT_RESPONSE;
    Accept(_,_),

    \* Given an authorization returns the message type URL it handles.
    \* @type: (AUTH) => MSG_TYPE_URL;
    MsgTypeURL(_),
    
    \* @ type: MSG_TYPE_URL;
    \* MsgTypeURL,

    \* The content of the messages to be executed.
    \* A set of, for example, Send messages or Stake messages
    \* @type: Set(Str);
    SdkMsgContent

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

--------------------------------------------------------------------------------
(******************************************************************************)
(* A grant is an allowance to execute a Msg by the grantee on behalf of the
granter. Grants are identified by combining granter address (the address 
bytes of the granter), grantee address (the address bytes of the grantee) 
and Authorization type (its type URL). Hence we only allow one grant for 
the (granter, grantee, Authorization) triple. *)
(******************************************************************************)
\* @typeAlias: GRANT_ID = [grantee: ADDRESS, granter: ADDRESS, msgTypeUrl: MSG_TYPE_URL];
\* @type: Set(GRANT_ID);
GrantIds == [
    granter: Address,
    grantee: Address,
    msgTypeUrl: MsgTypeUrls
]

\* @type: (GRANT_ID) => Bool;
IsValid(g) == g.granter # g.grantee

\* @type: Set(GRANT_ID);
ValidGrantIds == { g \in GrantIds: IsValid(g) }

\* Time when the grant will expire with respect to the moment when the related
\* event happens. If none, then the grant doesn't have an expiration time and 
\* other conditions in the authorization may apply to invalidate it.
\* @typeAlias: EXPIRATION_TIME = Str;
\* @type: Set(EXPIRATION_TIME);
ExpirationTimes == {"past", "future", "none"}

\* Grant gives permissions to execute the provide method with expiration time.
\* https://github.com/cosmos/cosmos-sdk/blob/c1b6ace7d542925b526cf3eef6df38a206eab8d8/x/authz/authz.pb.go#L74

\* @typeAlias: GRANT = [authorization: AUTH, expirationTime: EXPIRATION_TIME];
\* @type: Set(GRANT);
Grants == [
    authorization: Authorization,
    expirationTime: ExpirationTimes
]

\* @type: GRANT;
NoGrant == [ authorization |-> NoAuthorization, expirationTime |-> "none" ]

\* @type: (GRANT_ID) => Bool;
HasGrant(g) == g \in DOMAIN grantStore

\* @type: (GRANT_ID) => Bool;
IsExpired(g) == grantStore[g].expirationTime = "past"

\* The action of deleting a grant from the KV store in the server.
\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/keeper.go#L204
DeleteGrant(g) == 
    grantStore' = [k \in DOMAIN grantStore \ {g} |-> grantStore[k]]

--------------------------------------------------------------------------------
(******************************************************************************)
(* MsgGrant is a request message to the Grant method. It declares authorization
to the grantee on behalf of the granter with the provided expiration time. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L36
\* @typeAlias: MSG_GRANT = [grant: GRANT, grantee: ADDRESS, granter: ADDRESS, type: Str];
\* @type: Set(MSG_GRANT);
MsgGrant == [
    type: {"grant"},
    granter: Address,
    grantee: Address,
    grant: Grants
]

(******************************************************************************)
(* A grant can be removed with the MsgRevoke message. MsgRevoke revokes any
authorization with the provided sdk.Msg type on the granter's account with 
that has been granted to the grantee. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L196
\* @typeAlias: MSG_REVOKE = [grantee: ADDRESS, granter: ADDRESS, msgTypeUrl: MSG_TYPE_URL, type: Str];
\* @type: Set(MSG_REVOKE);
MsgRevoke == [
    type: {"revoke"},
    granter: Address,
    grantee: Address,
    msgTypeUrl: MsgTypeUrls
]

\* @type: (MSG_REVOKE) => GRANT_ID;
grantIdOfRevoke(msgRevoke) == [
    grantee |-> msgRevoke.grantee,
    granter |-> msgRevoke.granter,
    msgTypeUrl |-> msgRevoke.msgTypeUrl
]

\* Messages to be executed, such as Send messages or Stake messages. The
\* content of a message depends on the implementation of the authorization 
\* logic. 
\* A signer of the message corresponds to the granter of the 
\* authorization. A message implements an Authorization interface (methods 
\* MsgTypeURL and Accept).
\* @typeAlias: SDK_MSG = [signer: ADDRESS, msgTypeUrl: MSG_TYPE_URL, content: Str];
\* @type: Set(SDK_MSG);
SdkMsgs == [
    signer: Address,
    msgTypeUrl: MsgTypeUrls,
    content: SdkMsgContent
]

(******************************************************************************)
(* MsgExec attempts to execute the provided messages using authorizations
granted to the grantee. Each message should have only one signer corresponding
to the granter of the authorization. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L116
\* @typeAlias: MSG_EXEC = [grantee: ADDRESS, msgs: Set(SDK_MSG), type: Str];
\* @type: Set(MSG_EXEC);
MsgExec == [
    type: {"exec"},

    grantee: Address,

	\* Each message must implement an Authorization interface. The x/authz module
	\* will try to find a grant matching (msg.signers[0], grantee, MsgTypeURL(msg))
	\* triple and validate it.
    msgs: SUBSET SdkMsgs \ {{}}
]

\* @typeAlias: EVENT = [g: GRANT_ID, type: Str];
\* @type: Set(EVENT);
ExpireEvents == [type: {"expire"}, g: ValidGrantIds]

\* @typeAlias: REQUEST_MSG = [grant: GRANT, grantee: ADDRESS, granter: ADDRESS, msgTypeUrl: MSG_TYPE_URL, msgs: Set(SDK_MSG), type: Str];
\* @type: Set(REQUEST_MSG);
RequestMessages == MsgGrant \cup MsgRevoke \cup MsgExec

--------------------------------------------------------------------------------
(******************************************************************************)
(* Responses *)
(******************************************************************************)

MsgGrantResponseErrors == {
    "none", 
    "granter-equal-grantee", 
    "authorization-expired", 
    "authorization-not-implemented", 
    "msgTypeURL-not-defined"
}

\* @typeAlias: RESPONSE_GRANT = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_GRANT);
MsgGrantResponses == [
    type: {"grant"}, 
    ok: BOOLEAN, 
    error: MsgGrantResponseErrors
]

MsgExecResponseErrors == {
    "none", 
    "granter-equal-grantee", 
    "grant-not-found", 
    "authorization-expired", 
    "authorization-not-implemented", 
    "msgTypeURL-not-defined"
}

\* @typeAlias: RESPONSE_EXEC = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_EXEC);
MsgExecResponses == [
    type: {"exec"}, 
    ok: BOOLEAN, 
    error: MsgExecResponseErrors
]

\* @typeAlias: RESPONSE_REVOKE = [ok: Bool, type: Str];
\* @type: Set(RESPONSE_REVOKE);
MsgRevokeResponses == [
    type: {"MsgRevokeResponses"}, 
    ok: BOOLEAN
]

\* @typeAlias: RESPONSE_MSG = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_MSG);
Responses == MsgGrantResponses \cup MsgExecResponses \cup MsgRevokeResponses

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

(*****************************************************************************)
(* The logic of accepting an Authorization is specific to each 
implementation. *)
(*****************************************************************************)
\* @ type: (GRANT_ID, SDK_MDG) => ACCEPT_RESPONSE;
\* Accept(grantId, msg) == CHOOSE r \in AcceptResponse: TRUE

\* GrantQueueItem contains the list of TypeURL of a sdk.Msg.
\* type GrantQueueItem struct {
\* 	// msg_type_urls contains the list of TypeURL of a sdk.Msg.
\* 	MsgTypeUrls []string
\* }

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/keeper.go#L90
\* @type: (ADDRESS, SDK_MSG) => ACCEPT_RESPONSE;
DispatchActionsOneMsg(grantee, msg) == 
    LET granter == msg.signer IN \* Actually, granter is the first of the list of signers.
    IF granter = grantee THEN 
        [accept |-> TRUE, delete |-> FALSE, updated |-> NoUpdate, error |-> "none"]
    ELSE
        LET g == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msg.msgTypeUrl] IN
        IF ~ HasGrant(g) THEN 
            [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "grant-not-found"]
        ELSE 
            LET grant == grantStore[g] IN
            IF grant.expirationTime = "past" THEN 
                [accept |-> FALSE, delete |-> FALSE, updated |-> NoUpdate, error |-> "authorization-expired"]
            ELSE 
                Accept(grant.auth, msg)

\* @type: (REQUEST_MSG, ACCEPT_RESPONSE) => Bool;
PostProcessExec(request, acceptResponse) == 
    LET msg == CHOOSE msg \in request.msgs: TRUE IN
    LET g == [granter |-> msg.signer, grantee |-> request.grantee, msgTypeUrl |-> msg.msgTypeUrl] IN
    IF acceptResponse.delete THEN
        DeleteGrant(g)
    ELSE IF acceptResponse.accept /\ acceptResponse.updated # NoUpdate THEN
        grantStore' = [grantStore EXCEPT ![g].authorization = acceptResponse.updated]
    ELSE
        UNCHANGED <<grantStore>>

\* https://github.com/cosmos/cosmos-sdk/blob/afab2f348ab36fe323b791d3fc826292474b678b/x/authz/keeper/msg_server.go#L72
\* @type: (MSG_EXEC) => <<RESPONSE_EXEC, ACCEPT_RESPONSE>>;
CallExec(msgExec) == 
    LET msg == CHOOSE msg \in msgExec.msgs: TRUE IN
    LET acceptResponse == DispatchActionsOneMsg(msgExec.grantee, msg) IN 
    LET execResponse == [
        type |-> "exec", 
        ok |-> acceptResponse.accept, 
        error |-> acceptResponse.error
    ] IN 
    <<execResponse, acceptResponse>>

-------------------------------------------------------------------------------
\* Just for the initial state
NoRequest == [type |-> "NoRequest"]
NoResponse == [type |-> "NoResponse"]

TypeOK == 
    /\ grantStore \in [ValidGrantIds -> Grants]
    /\ lastRequest \in RequestMessages \cup {NoRequest}
    /\ lastResponse \in Responses \cup {NoResponse}
    /\ lastEvent \in RequestMessages \cup {NoRequest} \cup ExpireEvents

-------------------------------------------------------------------------------

Init ==
    /\ grantStore = [g \in {} |-> NoGrant]
    /\ lastRequest = NoRequest
    /\ lastResponse = NoResponse
    /\ lastEvent = NoRequest

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
        \* msgTypeUrl == MsgTypeURL
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
                    grantStore' = [grantStore EXCEPT ![g] = grant]
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
                    DeleteGrant(g)
                ELSE 
                    UNCHANGED grantStore
            /\ lastResponse' = response

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
    \/ \E grantee \in Address, msgs \in SUBSET SdkMsgs \ {{}}: 
        RequestExec(grantee, msgs)

--------------------------------------------------------------------------------

================================================================================
Created by Hernán Vanzetto on 10 August 2022
