---------------------- MODULE GenericAuthorization -----------------------------
(******************************************************************************)
(* GenericAuthorization gives unrestricted permission to execute the provided
Msg on behalf of granter's account. *)
(******************************************************************************)
EXTENDS MsgTypes

CONSTANT
    \* @typeAlias: ACCOUNT = Str;
    \* @type: Set(ACCOUNT);
    Accounts, 
    \* @typeAlias: VALIDATOR = Str;
    \* @type: Set(VALIDATOR);
    Validators

\* Types of messages allowed to be granted permission
\* @type: Set(MSG_TYPE_URL);
MsgTypeUrls == MsgTypes

\* @type: Set(SDK_MSG);
SdkMsg == [
    typeUrl: MsgTypeUrls 
]

--------------------------------------------------------------------------------

\* GenericAuthorization gives the grantee unrestricted permissions to execute
\* the provided method on behalf of the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/authz.pb.go#L34
\* @typeAlias: AUTH = [msgTypeUrl: MSG_TYPE_URL];
\* @type: Set(AUTH);
Authorization == [
    type: {"generic-authorization"},

    \* In the code this field is called Msg. It's a message type, identified by
    \* its type URL. The authorization grants unrestricted permission to
    \* execute.
    msgTypeUrl: MsgTypeUrls
]

\* @type: (AUTH) => Str;
AuthValidateBasic(auth) == "none"

--------------------------------------------------------------------------------

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/generic_authorization.go#L17
\* @type: (AUTH) => MSG_TYPE_URL;
MsgTypeURL(auth) == 
    auth.msgTypeUrl

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/generic_authorization.go#L22
\* @typeAlias: ACCEPT_RESPONSE = [accept: Bool, delete: Bool, updated: AUTH, error: Str];
\* @type: (AUTH, SDK_MSG) => ACCEPT_RESPONSE;
Accept(auth, msg) == [
    accept |-> TRUE, 
    delete |-> FALSE, 
    updated |-> auth, 
    error |-> "none"
]

================================================================================
Created by Hern??n Vanzetto on 10 August 2022
