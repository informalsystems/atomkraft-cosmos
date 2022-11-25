---------------------- MODULE GenericAuthorization -----------------------------
(******************************************************************************)
(* GenericAuthorization gives unrestricted permission to execute the provided
Msg on behalf of granter's account. *)
(******************************************************************************)
EXTENDS MsgTypes

CONSTANT
    \* @type: Set($account);
    Accounts, 
    \* @type: Set($validator);
    Validators

\* Types of messages allowed to be granted permission
\* @type: Set($msgTypeUrl);
MsgTypeUrls == MsgTypes

\* @type: Set($sdkMsg);
SdkMsg == [
    typeUrl: MsgTypeUrls 
]

--------------------------------------------------------------------------------

\* GenericAuthorization gives the grantee unrestricted permissions to execute
\* the provided method on behalf of the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/authz.pb.go#L34
\* @type: Set($auth);
Authorization == [
    type: {"generic-authorization"},

    \* In the code this field is called Msg. It's a message type, identified by
    \* its type URL. The authorization grants unrestricted permission to
    \* execute.
    msgTypeUrl: MsgTypeUrls
]

\* @type: ($auth) => Str;
AuthValidateBasic(auth) == "none"

--------------------------------------------------------------------------------

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/generic_authorization.go#L17
\* @type: ($auth) => $msgTypeUrl;
MsgTypeURL(auth) == 
    auth.msgTypeUrl

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/generic_authorization.go#L22
\* @typeAlias: acceptResponse = {accept: Bool, delete: Bool, updated: $auth, error: Str};
\* @type: ($auth, $sdkMsg) => $acceptResponse;
Accept(auth, msg) == [
    accept |-> TRUE, 
    delete |-> FALSE, 
    updated |-> auth, 
    error |-> "none"
]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
