-------------------------------- MODULE Authz ----------------------------------
(******************************************************************************)
(* Official Authz documentation: https://docs.cosmos.network/v0.46/modules/authz/ *)
(* ADR: https://github.com/cosmos/cosmos-sdk/blob/main/docs/architecture/adr-030-authz-module.md *)
(******************************************************************************)
EXTENDS AuthzMessages, AuthzMethods, Maps, Integers

VARIABLES    
    \* @typeAlias: event = {authorization: $auth, grant: $grant, grantee: $account, granter: $account, msgTypeUrl: $msgTypeUrl, msg: $sdkMsg, grantId: $grantId, type: Str};
    \* @type: $event;
    event,

    \* @type: $responseMsg;
    expectedResponse

--------------------------------------------------------------------------------
(******************************************************************************)
(* Initial state                                                              *)
(******************************************************************************)

\* Only for the initial state.
NoEvent == [type |-> "no-event"]

\* EmptyMap is not accepted by Apalache's typechecker.
\* @type: $grantId -> $grant;
EmptyStore == [x \in {} |-> NoGrant]

\* @typeAlias: expireEvent = {authorization: $auth, grantId: $grantId, type: Str};
\* @type: Set($expireEvent);
ExpireEvents == [
    type: {"expire"}, 
    grantId: { grantId \in GrantIds: grantId.granter # grantId.grantee },
    authorization: Authorization
]

Init ==
    /\ grantStore = EmptyStore
    /\ event = NoEvent
    /\ expectedResponse = NoResponse

--------------------------------------------------------------------------------
(******************************************************************************)
(* State actions                                                              *)
(******************************************************************************)

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
\* @type: ($account, $account, $grant) => Bool;
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

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/keeper/keeper.go#L205
\* @type: ($grantId, Bool) => Bool;
DeleteGrant(grantId, condition) ==
    IF condition THEN
        grantStore' = MapRemove(grantStore, grantId)
    ELSE 
        UNCHANGED grantStore

(******************************************************************************)
(* Request to revoke a grant.                                                 *)
(******************************************************************************)
\* @type: ($account, $account, $msgTypeUrl) => Bool;
RequestRevoke(granter, grantee, msgTypeUrl) == 
    LET 
        \* @type: REQUEST_MSG;
        msg == [type |-> "request-revoke", granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msgTypeUrl] 
        response == SendMsgRevoke(msg) 
        \* @type: $grantId;
        grantId == [granter |-> granter, grantee |-> grantee, msgTypeUrl |-> msgTypeUrl]
    IN
    /\ event' = msg
    /\ expectedResponse' = response
    /\ DeleteGrant(grantId, response.ok)

(******************************************************************************)
(* Request to execute a message on behalf of a grantee.                       *)
(******************************************************************************)
\* @type: ($account, $sdkMsg) => Bool;
RequestExecute(grantee, msg) ==
    LET 
        request == [type |-> "request-execute", grantee |-> grantee, msg |-> msg]
        \* @type: <<RESPONSE_EXEC, $acceptResponse>>;
        response == SendMsgExecute(request)
        \* @type: $acceptResponse;
        acceptResponse == response[2]
        \* @type: $grantId;
        grantId == [granter |-> GetSigner(msg), grantee |-> grantee, msgTypeUrl |-> msg.typeUrl] 
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
    LET grant == grantStore[grantId] IN
    /\ ExistsGrantFor(grantId)
    /\ grant.expiration = "future"
    /\ event' = [type |-> "expire", grantId |-> grantId, authorization |-> grant.authorization]
    /\ expectedResponse' = NoResponse
    \* DequeueAndDeleteExpiredGrants: https://github.com/cosmos/cosmos-sdk/blob/25e7f9bee2b35f0211b0e323dd062b55bef987b7/x/authz/keeper/keeper.go#L379
    /\ DeleteGrant(grantId, TRUE)

--------------------------------------------------------------------------------
Next == 
    \/ \E granter, grantee \in Accounts, grant \in Grants: 
        RequestGrant(granter, grantee, grant)
    \/ \E grantId \in GrantIds: 
        RequestRevoke(grantId.granter, grantId.grantee, grantId.msgTypeUrl)
    \* NB: The implementation allows to send more than one message in an Exec
    \* request. Here we model execution requests of only one message per call.
    \/ \E grantee \in Accounts, msg \in SdkMsg: 
        RequestExecute(grantee, msg)
    \/ \E grantId \in GrantIds: 
        Expire(grantId)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Model invariants                                                           *)
(******************************************************************************)

TypeOK == 
    /\ IsMap(grantStore, GrantIds, Grants \cup {NoGrant})
    /\ event \in RequestMessages \cup ExpireEvents \cup {NoEvent}
    /\ expectedResponse \in Responses \cup {NoResponse}

NoExpiredGrantInStore == 
    \A grantId \in DOMAIN grantStore: 
        grantStore[grantId].expiration # "past"

RequestGrantInv1 ==
    /\ event.type = "request-grant"
    /\ MsgGrantValidateBasic(event) # "none"
    /\ event.granter # event.grantee
    /\ event.grant.authorization.type = "stake-authorization"
    /\ event.grant.authorization.maxTokens = -1
    => expectedResponse.error = NEGATIVE_COIN_AMOUNT

UnRedelegateFailToExecute ==
    LET grantId == grantIdOfMsgExecute(event) IN
    /\ event.type = "request-execute"
    /\ SdkMsgValidateBasic(event.msg) = "none"
    /\ grantId.granter # grantId.grantee
    /\ ExistsGrantFor(grantId) 
    /\ event.msg.typeUrl \in {UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL}
    => expectedResponse.error = FAILED_TO_EXECUTE

ExecuteInvalidMessageInv ==
    LET grantId == grantIdOfMsgExecute(event) IN
    /\ event.type = "request-execute"
    /\ SdkMsgValidateBasic(event.msg) # "none"
    => expectedResponse.error = SdkMsgValidateBasic(event.msg)

ExecuteInv1 ==
    LET grantId == grantIdOfMsgExecute(event) IN
    /\ event.type = "request-execute"
    /\ event.msg.typeUrl \notin {UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL}
    /\ SdkMsgValidateBasic(event.msg) # "none"
    => expectedResponse.error = SdkMsgValidateBasic(event.msg)

ExecuteInv2 ==
    LET grantId == grantIdOfMsgExecute(event) IN
    /\ event.type = "request-execute"
    /\ event.msg.typeUrl \notin {UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL}
    /\ SdkMsgValidateBasic(event.msg) = "none"
    /\ grantId.granter # grantId.grantee
    /\ ~ ExistsGrantFor(grantId) 
    => expectedResponse.error = AUTH_NOT_FOUND

ExecuteInv3 ==
    LET grantId == grantIdOfMsgExecute(event) IN
    /\ event.type = "request-execute"
    /\ event.msg.typeUrl \notin {UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL}
    /\ grantId.granter # grantId.grantee
    /\ ExistsGrantFor(grantId) 
    /\ grantStore[grantId].expiration = "past"
    => expectedResponse.error = AUTH_EXPIRED

ValidRevokeCannotAuthNotFound ==
    LET grantId == grantIdOfMsgRevoke(event) IN
    /\ event.type = "request-revoke"
    /\ grantId.granter # grantId.grantee
    /\ ExistsGrantFor(grantId) 
    => expectedResponse.error # AUTH_NOT_FOUND

Inv == 
    /\ TypeOK
    /\ NoExpiredGrantInStore
    /\ RequestGrantInv1
    /\ UnRedelegateFailToExecute
    /\ ExecuteInvalidMessageInv
    /\ ExecuteInv1
    /\ ExecuteInv2
    /\ ExecuteInv3
    /\ ValidRevokeCannotAuthNotFound

================================================================================
Created by Hernán Vanzetto on 10 August 2022
