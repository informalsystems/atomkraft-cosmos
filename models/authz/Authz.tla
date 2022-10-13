-------------------------------- MODULE Authz ----------------------------------
(******************************************************************************)
(* Official Authz documentation: https://docs.cosmos.network/v0.46/modules/authz/ *)
(* ADR: https://github.com/cosmos/cosmos-sdk/blob/main/docs/architecture/adr-030-authz-module.md *)
(******************************************************************************)
EXTENDS AuthzMessages, AuthzService, Maps, Integers

VARIABLES    
    \* @typeAlias: EVENT = [authorization: AUTH, grant: GRANT, grantee: ACCOUNT, granter: ACCOUNT, msgTypeUrl: MSG_TYPE_URL, msg: SDK_MSG, grantId: GRANT_ID, type: Str];
    \* @type: EVENT;
    event,

    \* @type: RESPONSE_MSG;
    expectedResponse

--------------------------------------------------------------------------------
\* Only for the initial state.
NoEvent == [type |-> "no-event"]

\* EmptyMap is not accepted by Apalache's typechecker.
\* @type: GRANT_ID -> GRANT;
EmptyStore == [x \in {} |-> NoGrant]

\* @typeAlias: EXPIRE_EVENT = [authorization: AUTH, grantId: GRANT_ID, type: Str];
\* @type: Set(EXPIRE_EVENT);
ExpireEvents == [
    type: {"expire"}, 
    grantId: ValidGrantIds,
    authorization: Authorization
]

TypeOK == 
    /\ IsMap(grantStore, ValidGrantIds, Grants \cup {NoGrant})
    /\ event \in RequestMessages \cup ExpireEvents \cup {NoEvent}
    /\ expectedResponse \in Responses \cup {NoResponse}

Init ==
    /\ grantStore = EmptyStore
    /\ event = NoEvent
    /\ expectedResponse = NoResponse

--------------------------------------------------------------------------------
(******************************************************************************)
(* Request to give a grant from a granter to a grantee.                       *)
(*                                                                            *)
(* From the code: "An authorization grant is created using the MsgGrant       *)
(* message. If there is already a grant for the (granter, grantee,            *)
(* Authorization) triple, then the new grant overwrites the previous one. To  *)
(* update or extend an existing grant, a new grant with the same (granter,    *)
(* grantee, Authorization) triple should be created."                         *)
(*                                                                            *)
(* The message handling should fail if:                                       *)
(* - both granter and grantee have the same address.                          *)
(* - provided Expiration time is less than current unix timestamp.            *)
(* - provided Grant.Authorization is not implemented.                         *)
(* - Authorization.MsgTypeURL() is not defined in the router (there is no     *)
(* defined handler in the app router to handle that Msg types).               *)
(******************************************************************************)
\* @type: (ACCOUNT, ACCOUNT, GRANT) => Bool;
RequestGrant(granter, grantee, grant) ==
    LET 
        msg == [type |-> "request-grant", granter |-> granter, grantee |-> grantee, grant |-> grant]
        grantId == grantIdOfMsgGrant(msg)
        response == SendMsgGrant(msg)
    IN
    /\ event' = msg
    /\ expectedResponse' = response
    /\ grantStore' = IF response.ok 
        THEN MapPut(grantStore, grantId, grant) 
        ELSE grantStore

\* https://github.com/cosmos/cosmos-sdk/blob/e09516f4795c637ab12b30bf732ce5d86da78424/x/authz/keeper/keeper.go#L204
\* @type: (GRANT_ID, Bool) => Bool;
DeleteGrant(grantId, condition) ==
    IF condition THEN
        grantStore' = MapRemove(grantStore, grantId)
    ELSE 
        UNCHANGED grantStore

(******************************************************************************)
(* Request to revoke a grant.                                                 *)
(******************************************************************************)
\* @type: (ACCOUNT, ACCOUNT, MSG_TYPE_URL) => Bool;
RequestRevoke(granter, grantee, msgTypeUrl) == 
    LET 
        \* @type: REQUEST_MSG;
        msg == [type |-> "request-revoke", granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msgTypeUrl] 
        response == SendMsgRevoke(msg) 
        \* @type: GRANT_ID;
        grantId == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msgTypeUrl]
    IN
    /\ event' = msg
    /\ expectedResponse' = response
    /\ DeleteGrant(grantId, response.ok)

(******************************************************************************)
(* Request to execute a message on behalf of a grantee.                       *)
(******************************************************************************)
\* @type: (ACCOUNT, SDK_MSG) => Bool;
RequestExecute(grantee, msg) ==
    LET 
        request == [type |-> "request-execute", grantee |-> grantee, msg |-> msg]
        \* @type: <<RESPONSE_EXEC, ACCEPT_RESPONSE>>;
        response == SendMsgExecute(request)
        \* @type: ACCEPT_RESPONSE;
        acceptResponse == response[2]
        \* @type: GRANT_ID;
        grantId == [granter |-> msg.signer, grantee |-> grantee, msgTypeUrl |-> msg.typeUrl] 
    IN
    /\ event' = request
    /\ expectedResponse' = response[1]
    /\ IF acceptResponse.updated # NoUpdate THEN
            grantStore' = [grantStore EXCEPT ![grantId].authorization = acceptResponse.updated]
        ELSE
            DeleteGrant(grantId, acceptResponse.delete)

(******************************************************************************)
(* Expire is the event in which a grant expiration time passes from being in  *)
(* the "future" to being in the "past". Note that the relation between        *)
(* different grants and their expirations may be lost (in real life, there    *)
(* could be a dependency: if A expires, then definitely B and C have to       *)
(* expire).                                                                   *)
(******************************************************************************)
Expire(grantId) ==
    /\ HasGrant(grantId)
    /\ ~ IsExpired(grantId)
    /\ grantStore[grantId].expiration = "future"
    /\ event' = [type |-> "expire", grantId |-> grantId, authorization |-> grantStore[grantId].authorization]
    /\ expectedResponse' = NoResponse
    \* DequeueAndDeleteExpiredGrants: https://github.com/cosmos/cosmos-sdk/blob/25e7f9bee2b35f0211b0e323dd062b55bef987b7/x/authz/keeper/keeper.go#L379
    /\ DeleteGrant(grantId, TRUE)

--------------------------------------------------------------------------------
NextAllowInvalidArguments == 
    \/ \E granter, grantee \in Accounts, grant \in Grants: 
        RequestGrant(granter, grantee, grant)
    \/ \E grantId \in GrantIds: 
        RequestRevoke(grantId.granter, grantId.grantee, grantId.msgTypeUrl)
    \/ \E grantId \in ValidGrantIds: 
        Expire(grantId)

NextOnlyWithValidArguments == 
    \/ \E granter, grantee \in Accounts, grant \in Grants: 
        /\ granter # grantee
        /\ grant.expiration # "past"
        /\ RequestGrant(granter, grantee, grant)
    \/ \E grantId \in ValidGrantIds: 
        /\ HasGrant(grantId)
        /\ ~ IsExpired(grantId)
        /\ RequestRevoke(grantId.granter, grantId.grantee, grantId.msgTypeUrl)
    \/ \E grantId \in ValidGrantIds: 
        Expire(grantId)

\* We keep action RequestExecute separated from the other actions to be able to 
\* check properties on grants without executing them. 
Next == 
    \* \/ NextOnlyWithValidArguments
    \/ NextAllowInvalidArguments
    \* NB: The implementation allows to send more than one message in an Exec
    \* request. We model execution requests of only one message per call.
    \/ \E grantee \in Accounts, msg \in SdkMsg: 
        RequestExecute(grantee, msg)
--------------------------------------------------------------------------------
(******************************************************************************)
(* Invariants                                                                 *)
(******************************************************************************)

NoExpiredGrantInStore == 
    \A grantId \in DOMAIN grantStore: 
        grantStore[grantId].expiration # "past"

UnRedelegateFailToExecute ==
    /\ event.type = "request-execute"
    /\ event.msg.typeUrl \in {UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL}
    => expectedResponse.error = FAILED_TO_EXECUTE

ValidRevokeCannotAuthNotFound ==
    LET grantId == grantIdOfMsgRevoke(event) IN
    /\ event.type = "request-revoke"
    /\ IsValid(grantId)
    /\ ~ HasGrant(grantId) 
    => expectedResponse.error # AUTH_NOT_FOUND

Inv == 
    /\ NoExpiredGrantInStore
    /\ UnRedelegateFailToExecute
    /\ ValidRevokeCannotAuthNotFound

================================================================================
Created by Hernán Vanzetto on 10 August 2022
