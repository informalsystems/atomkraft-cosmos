----------------------------- MODULE AuthzMessages -----------------------------
(******************************************************************************)
(* Authz messages as defined in                                               *)
(*    https://github.com/cosmos/cosmos-sdk/blob/main/proto/cosmos/authz/v1beta1/tx.proto *)
(******************************************************************************)
EXTENDS Grants

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

\* @type: (MSG_EXEC) => GRANT_ID;
grantIdOfMsgExecute(msgExec) == [
    grantee |-> msgExec.grantee,
    granter |-> msgExec.msg.signer,
    msgTypeUrl |-> msgExec.msg.typeUrl
]

\* @typeAlias: EXPIRE_EVENT = [grantId: GRANT_ID, type: Str];
\* @type: Set(EXPIRE_EVENT);
ExpireEvents == [
    type: {"expire"}, 
    grantId: ValidGrantIds
]

\* @typeAlias: REQUEST_MSG = [grant: GRANT, grantee: ACCOUNT, granter: ACCOUNT, msgTypeUrl: MSG_TYPE_URL, msg: SDK_MSG, type: Str];
\* @type: Set(REQUEST_MSG);
RequestMessages == MsgGrant \cup MsgRevoke \cup MsgExec

--------------------------------------------------------------------------------
(******************************************************************************)
(* Responses                                                                  *)
(******************************************************************************)

MsgGrantResponseErrors == {
    "none", 
    "granter-equal-grantee", 
    "authorization-expired"
    \* "authorization-not-implemented", 
    \* "msgTypeURL-not-defined"
}

\* @typeAlias: RESPONSE_GRANT = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_GRANT);
MsgGrantResponses == [
    type: {"response-grant"}, 
    ok: BOOLEAN, 
    error: MsgGrantResponseErrors
]

--------------------------------------------------------------------------------
MsgExecResponseErrors == {
    "none", 
    "grant-not-found", 
    "authorization-expired", 
    
    \* For SendAuthorization and StakeAuthorization
    "insufficient-amount",
    "account-not-allowed",
    "validator-not-allowed",
    "validator-denied",
    "invalid-request"
}

\* @typeAlias: RESPONSE_EXEC = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_EXEC);
MsgExecResponses == [
    type: {"response-execute"}, 
    ok: BOOLEAN, 
    error: MsgExecResponseErrors
]

--------------------------------------------------------------------------------
MsgRevokeResponseErrors == {
    "none", 
    "grant-not-found"
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
