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
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/tx.pb.go#L36
\* @typeAlias: MSG_GRANT = [grant: GRANT, grantee: ACCOUNT, granter: ACCOUNT, type: Str];
\* @type: Set(MSG_GRANT);
MsgGrant == [
    type: {"request-grant"},
    granter: Accounts,
    grantee: Accounts,
    grant: Grants
]

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/msgs.go#L53
\* @type: (MSG_GRANT) => Str;
MsgGrantValidateBasic(msg) ==
    IF msg.granter = msg.grantee THEN 
        GRANTER_EQUALS_GRANTEE
    ELSE
        GrantValidateBasic(msg.grant)

(******************************************************************************)
(* A grant can be removed with the MsgRevoke message. MsgRevoke revokes any
authorization with the provided sdk.Msg type on the granter's account with 
that has been granted to the grantee. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/tx.pb.go#L196
\* @typeAlias: MSG_REVOKE = [grantee: ACCOUNT, granter: ACCOUNT, msgTypeUrl: MSG_TYPE_URL, type: Str];
\* @type: Set(MSG_REVOKE);
MsgRevoke == [
    type: {"request-revoke"},
    granter: Accounts,
    grantee: Accounts,
    msgTypeUrl: MsgTypeUrls
]

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/msgs.go#L139
\* @type: (MSG_REVOKE) => Str;
MsgRevokeValidateBasic(msg) ==
    IF msg.granter = msg.grantee THEN 
        GRANTER_EQUALS_GRANTEE
    ELSE
        "none"

(******************************************************************************)
(* MsgExec attempts to execute the provided messages using authorizations
granted to the grantee. Each message should have only one signer corresponding
to the granter of the authorization. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/tx.pb.go#L116
\* @typeAlias: MSG_EXEC = [grantee: ACCOUNT, msg: SDK_MSG, type: Str];
\* @type: Set(MSG_EXEC);
MsgExec == [
    type: {"request-execute"},

    grantee: Accounts,

    \* Each message must implement an Authorization interface. The x/authz module
    \* will try to find a grant matching (GetSigner(msg), grantee, MsgTypeURL(msg))
    \* triple and validate it.
    msg: SdkMsg
]

\* @typeAlias: REQUEST_MSG = [grant: GRANT, grantee: ACCOUNT, granter: ACCOUNT, msgTypeUrl: MSG_TYPE_URL, msg: SDK_MSG, type: Str];
\* @type: Set(REQUEST_MSG);
RequestMessages == MsgGrant \cup MsgRevoke \cup MsgExec

--------------------------------------------------------------------------------
\* @type: (SDK_MSG) => MSG_TYPE_URL;
GetSigner(sdkMsg) ==
    CASE sdkMsg.typeUrl = SEND_TYPE_URL -> 
        \* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/bank/types/msgs.go#L56
        sdkMsg.fromAddress
      [] sdkMsg.typeUrl \in {DELEGATE_TYPE_URL, UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL} -> 
        \* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/msg.go#L215
        sdkMsg.delegatorAddress

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
    granter |-> GetSigner(msg.msg),
    msgTypeUrl |-> msg.msg.typeUrl
]

grantIdOfMsg(msg) ==
    CASE msg.type = "request-grant" -> grantIdOfMsgGrant(msg)
      [] msg.type = "request-revoke" ->  grantIdOfMsgRevoke(msg)
      [] msg.type = "request-execute" -> grantIdOfMsgExecute(msg)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Responses                                                                  *)
(******************************************************************************)

\* @type: Set(Str);
MsgGrantResponseErrors == {
    GRANTER_EQUALS_GRANTEE, 
    INVALID_EXPIRATION,
    NEGATIVE_COIN_AMOUNT,
    SPEND_LIMIT_MUST_BE_POSITIVE,
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
    INVALID_COINS,

    \* For StakeAuthorization
    CANNOT_DELEGATE_TO_VALIDATOR,
    NEGATIVE_COIN_AMOUNT,
    INVALID_COINS,
    INVALID_DELEGATION_AMOUNT,
    INVALID_SHARES_AMOUNT,
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
    AUTH_NOT_FOUND,
    GRANTER_EQUALS_GRANTEE,
    "none"
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
Created by Hern??n Vanzetto on 10 August 2022
