---------------------- MODULE GenericAuthorization -----------------------------
(******************************************************************************)
(* GenericAuthorization gives unrestricted permission to execute the provided
Msg on behalf of granter's account. *)
(******************************************************************************)

CONSTANT
    \* @typeAlias: ADDRESS = Str;
    \* @type: Set(ADDRESS);
    Address, 
    \* @typeAlias: MSG_TYPE_URL = Str;
    \* @type: MSG_TYPE_URL;
    GenericMsgTypeUrl

AuthorizationTypes == { GenericMsgTypeUrl }

\* @ typeAlias: SDK_MSG_CONTENT = [type: MSG_TYPE_URL];
\* @typeAlias: SDK_MSG_CONTENT = [amount: COINS, fromAddress: ADDRESS, toAddress: ADDRESS, delegatorAddress: ADDRESS, validatorAddress: ADDRESS, validatorSrcAddress: ADDRESS, validatorSrcAddress: ADDRESS, validatorDstAddress: ADDRESS, type: MSG_TYPE_URL];
\* @type: Set(SDK_MSG_CONTENT);
SdkMsgContent == [type: {GenericMsgTypeUrl}]

\* Types of messages allowed to be granted permission
\* @type: Set(MSG_TYPE_URL);
MsgTypeUrls == { GenericMsgTypeUrl }

--------------------------------------------------------------------------------

\* GenericAuthorization gives the grantee unrestricted permissions to execute
\* the provided method on behalf of the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/c1b6ace7d542925b526cf3eef6df38a206eab8d8/x/authz/authz.pb.go#L34
\* @typeAlias: AUTH = [type: Str, msg: MSG_TYPE_URL];
\* @type: Set(AUTH);
Authorization == [
    type: {"generic"},
    
    \* Msg, identified by it's type URL, to grant unrestricted permissions to execute.
    msg: MsgTypeUrls
]

\* @type: AUTH;
NoAuthorization == [ type |-> "NoAuthorization" ]

--------------------------------------------------------------------------------

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/generic_authorization.go#L17
\* @type: (AUTH) => MSG_TYPE_URL;
MsgTypeURL(auth) == auth.msg

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/generic_authorization.go#L22
\* @type: (AUTH, SDK_MSG) => ACCEPT_RESPONSE;
Accept(auth, msg) == [
    accept |-> TRUE, 
    delete |-> FALSE, 
    updated |-> auth, 
    error |-> "none"
]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
