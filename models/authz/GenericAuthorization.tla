---------------------- MODULE GenericAuthorization -----------------------------
(******************************************************************************)
(* GenericAuthorization gives unrestricted permission to execute the provided
Msg on behalf of granter's account. *)
(******************************************************************************)

CONSTANT
    \* @typeAlias: ACCOUNT = Str;
    \* @type: Set(ACCOUNT);
    Accounts, 
    \* @typeAlias: VALIDATOR = Str;
    \* @type: Set(VALIDATOR);
    Validators,
    \* @typeAlias: MSG_TYPE_URL = Str;
    \* @type: Set(MSG_TYPE_URL);
    GenericAuthTypes

\* Types of messages allowed to be granted permission
\* @type: Set(MSG_TYPE_URL);
MsgTypeUrls == GenericAuthTypes

\* @typeAlias: SDK_MSG_CONTENT = [typeUrl: MSG_TYPE_URL];
\* @type: Set(SDK_MSG_CONTENT);
SdkMsgContent == [ typeUrl: GenericAuthTypes ]

--------------------------------------------------------------------------------

\* GenericAuthorization gives the grantee unrestricted permissions to execute
\* the provided method on behalf of the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/c1b6ace7d542925b526cf3eef6df38a206eab8d8/x/authz/authz.pb.go#L34
\* @typeAlias: AUTH = [authorizationType: MSG_TYPE_URL];
\* @type: Set(AUTH);
Authorization == [
    \* In the code this field is called Msg. The message type, identified by it's type
    \* URL, to grant unrestricted permissions to execute.
    authorizationType: MsgTypeUrls
]

--------------------------------------------------------------------------------

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/generic_authorization.go#L17
\* @type: (AUTH) => MSG_TYPE_URL;
MsgTypeURL(auth) == 
    auth.authorizationType

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/generic_authorization.go#L22
\* @typeAlias: ACCEPT_RESPONSE = [accept: Bool, delete: Bool, updated: AUTH, error: Str];
\* @type: (AUTH, SDK_MSG) => ACCEPT_RESPONSE;
Accept(auth, msg) == [
    accept |-> TRUE, 
    delete |-> FALSE, 
    updated |-> auth, 
    error |-> "none"
]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
