----------------------------- MODULE AuthzMessages -----------------------------
(******************************************************************************)
(* Authz messages as defined in                                               *)
(*    https://github.com/cosmos/cosmos-sdk/blob/main/proto/cosmos/authz/v1beta1/tx.proto *)
(******************************************************************************)
EXTENDS MsgTypes, MsgErrors, Grants

(******************************************************************************)
(* MsgGrant is a request message to the Grant method. It declares authorization
to the grantee on behalf of the granter with the provided expiration time. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L36
\* @typeAlias: MSG_GRANT = [grant: GRANT, grantee: ACCOUNT, granter: ACCOUNT, type: Str];
\* @type: Set(MSG_GRANT);
MsgGrant == [
    type: {"request-grant"},
    granter: Accounts,
    grantee: Accounts,
    grant: Grants
]

(******************************************************************************)
(* A grant can be removed with the MsgRevoke message. MsgRevoke revokes any
authorization with the provided sdk.Msg type on the granter's account with 
that has been granted to the grantee. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L196
\* @typeAlias: MSG_REVOKE = [grantee: ACCOUNT, granter: ACCOUNT, msgTypeUrl: MSG_TYPE_URL, type: Str];
\* @type: Set(MSG_REVOKE);
MsgRevoke == [
    type: {"request-revoke"},
    granter: Accounts,
    grantee: Accounts,
    msgTypeUrl: MsgTypeUrls
]

(******************************************************************************)
(* MsgExec attempts to execute the provided messages using authorizations
granted to the grantee. Each message should have only one signer corresponding
to the granter of the authorization. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L116
\* @typeAlias: MSG_EXEC = [grantee: ACCOUNT, msg: SDK_MSG, type: Str];
\* @type: Set(MSG_EXEC);
MsgExec == [
    type: {"request-execute"},

    grantee: Accounts,

    \* Each message must implement an Authorization interface. The x/authz module
    \* will try to find a grant matching (msg.signers[0], grantee, MsgTypeURL(msg))
    \* triple and validate it.
    msg: SdkMsg
]

\* @typeAlias: REQUEST_MSG = [grant: GRANT, grantee: ACCOUNT, granter: ACCOUNT, msgTypeUrl: MSG_TYPE_URL, msg: SDK_MSG, type: Str];
\* @type: Set(REQUEST_MSG);
RequestMessages == MsgGrant \cup MsgRevoke \cup MsgExec

--------------------------------------------------------------------------------
\* @type: (MSG_GRANT) => GRANT_ID;
grantIdOfMsgGrant(msg) == [
    grantee |-> msg.grantee,
    granter |-> msg.granter,
    msgTypeUrl |-> MsgTypeURL(msg.grant.authorization)
]

\* @type: (MSG_REVOKE) => GRANT_ID;
grantIdOfMsgRevoke(msg) == [
    grantee |-> msg.grantee,
    granter |-> msg.granter,
    msgTypeUrl |-> msg.msgTypeUrl
]

\* @type: (MSG_EXEC) => GRANT_ID;
grantIdOfMsgExecute(msg) == [
    grantee |-> msg.grantee,
    granter |-> msg.msg.signer,
    msgTypeUrl |-> msg.msg.typeUrl
]

\* grantIdOf(msg) ==
\*     CHOOSE grantId \in GrantIds: 
\*         CASE msg.type = "request-grant" -> grantId = grantIdOfMsgGrant(msg)
\*           [] msg.type = "request-revoke" -> grantId = grantIdOfMsgRevoke(msg)
\*           [] msg.type = "request-execute" -> grantId = grantIdOfMsgExecute(msg)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Responses                                                                  *)
(******************************************************************************)

\* @type: Set(Str);
MsgGrantResponseErrors == {
    GRANTER_EQUALS_GRANTEE, 
    INVALID_EXPIRATION,
    "none"
}

\* @typeAlias: RESPONSE_GRANT = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_GRANT);
MsgGrantResponses == [
    type: {"response-grant"}, 
    ok: BOOLEAN, 
    error: MsgGrantResponseErrors
]

--------------------------------------------------------------------------------

\* @type: Set(Str);
MsgExecResponseErrors == {
    AUTH_NOT_FOUND,
    AUTH_EXPIRED,
    NO_DELEGATION,

    \* For SendAuthorization:
    ADDRESS_NOT_ALLOWED,
    INSUFFICIENT_AMOUNT, 
    SPEND_LIMIT_IS_NIL,
    SPEND_LIMIT_IS_NEGATIVE,

    \* For StakeAuthorization
    CANNOT_DELEGATE_TO_VALIDATOR,
    NEGATIVE_COIN_AMOUNT,
    INVALID_DELEGATION_AMOUNT,
    FAILED_TO_EXECUTE,

    "none"
}

\* @typeAlias: RESPONSE_EXEC = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_EXEC);
MsgExecResponses == [
    type: {"response-execute"}, 
    ok: BOOLEAN, 
    error: MsgExecResponseErrors
]

--------------------------------------------------------------------------------
\* @type: Set(Str);
MsgRevokeResponseErrors == {
    "none", 
    AUTH_NOT_FOUND,
    GRANTER_EQUALS_GRANTEE
}

\* @typeAlias: RESPONSE_REVOKE = [ok: Bool, type: Str];
\* @type: Set(RESPONSE_REVOKE);
MsgRevokeResponses == [
    type: {"response-revoke"}, 
    ok: BOOLEAN,
    error: MsgRevokeResponseErrors
]

--------------------------------------------------------------------------------
\* For the initial state and expire events.
NoResponse == [
    type |-> "no-response",
    ok |-> TRUE,
    error |-> "none"
]

\* @typeAlias: RESPONSE_MSG = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_MSG);
Responses == MsgGrantResponses \cup MsgExecResponses \cup MsgRevokeResponses

================================================================================
Created by Hernán Vanzetto on 10 August 2022
