-------------------------- MODULE AuthzGeneric ---------------------------------
(******************************************************************************)
(* GenericAuthorization gives unrestricted permission to execute the provided
Msg on behalf of granter's account. *)
(******************************************************************************)

CONSTANT
    \* @type: Str;
    GenericMsgTypeUrl

AuthorizationTypes == { GenericMsgTypeUrl }

GenericMsg == [

]

\* GenericAuthorization gives the grantee unrestricted permissions to execute
\* the provided method on behalf of the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/c1b6ace7d542925b526cf3eef6df38a206eab8d8/x/authz/authz.pb.go#L34
GenericAuthorization == [
    type: {"GenericAuthorization"},
    
    \* Msg, identified by it's type URL, to grant unrestricted permissions to execute.
    msg: AuthorizationTypes
]

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/generic_authorization.go#L17
MsgTypeURL(auth) == auth.msg

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/generic_authorization.go#L22
\* @type: SEND_MSG => ACCEPT_RESPONSE;
Accept(auth, msg) == [
    accept |-> TRUE, 
    delete |-> FALSE, 
    updated |-> auth, 
    error |-> "none"
]

INSTANCE Authz WITH 
    MsgTypeUrls <- AuthorizationTypes,
    Authorization <- GenericAuthorization,
    \* SdkMsgs <- ??,
    MsgTypeURL <- MsgTypeURL,
    Accept <- Accept

================================================================================
Created by Hernán Vanzetto on 10 August 2022
