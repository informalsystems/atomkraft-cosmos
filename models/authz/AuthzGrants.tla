----------------------------- MODULE AuthzGrants -------------------------------
(******************************************************************************)

(******************************************************************************)
CONSTANTS
    \* @typeAlias: ADDRESS = Str;
    \* @type: Set(ADDRESS);
    Address

--------------------------------------------------------------------------------
CONSTANTS 
    \* @typeAlias: MSG_TYPE_URL = Str;
    \* @type: Set(MSG_TYPE_URL);
    GenericAuthTypes,
    \* @typeAlias: COINS = Int;
    \* @type: Set(COINS);
    Coins

--------------------------------------------------------------------------------
Generic == INSTANCE GenericAuthorization
Send == INSTANCE SendAuthorization
Stake == INSTANCE StakeAuthorization

MsgTypeUrls == Generic!MsgTypeUrls \cup Send!MsgTypeUrls \cup Stake!MsgTypeUrls
Authorization == Generic!Authorization \cup Send!Authorization \cup Stake!Authorization

\* @typeAlias: SDK_MSG_CONTENT = [amount: COINS, fromAddress: ADDRESS, toAddress: ADDRESS, delegatorAddress: ADDRESS, validatorAddress: ADDRESS, validatorSrcAddress: ADDRESS, validatorSrcAddress: ADDRESS, validatorDstAddress: ADDRESS, typeUrl: MSG_TYPE_URL];
SdkMsgContent == Generic!SdkMsgContent \cup Send!SdkMsgContent \cup Stake!SdkMsgContent

--------------------------------------------------------------------------------
(******************************************************************************)
(* A grant is an allowance to execute a Msg by the grantee on behalf of the
granter. Grants are identified by combining granter address (the address 
bytes of the granter), grantee address (the address bytes of the grantee) 
and Authorization type (its type URL). Hence we only allow one grant for 
the (granter, grantee, Authorization) triple. *)
(******************************************************************************)
\* @typeAlias: GRANT_ID = [grantee: ADDRESS, granter: ADDRESS, msgTypeUrl: MSG_TYPE_URL];
\* @type: Set(GRANT_ID);
GrantIds == [
    granter: Address,
    grantee: Address,
    msgTypeUrl: MsgTypeUrls
]

\* @type: (GRANT_ID) => Bool;
IsValid(g) == g.granter # g.grantee

\* @type: Set(GRANT_ID);
ValidGrantIds == { g \in GrantIds: IsValid(g) }

\* Time when the grant will expire with respect to the moment when the related
\* event happens. If none, then the grant doesn't have an expiration time and 
\* other conditions in the authorization may apply to invalidate it.
\* @typeAlias: EXPIRATION_TIME = Str;
\* @type: Set(EXPIRATION_TIME);
ExpirationTimes == {"past", "future", "none"}

\* Grant gives permissions to execute the provide method with expiration time.
\* https://github.com/cosmos/cosmos-sdk/blob/c1b6ace7d542925b526cf3eef6df38a206eab8d8/x/authz/authz.pb.go#L74
\* @typeAlias: GRANT = [authorization: AUTH, expirationTime: EXPIRATION_TIME];
\* @type: Set(GRANT);
Grants == [
    authorization: Authorization,
    expirationTime: ExpirationTimes
]

\* @type: AUTH;
NoAuthorization == [ type |-> "NoAuthorization" ]

\* @type: GRANT;
NoGrant == [ authorization |-> NoAuthorization, expirationTime |-> "none" ]

--------------------------------------------------------------------------------
(******************************************************************************)
(* MsgGrant is a request message to the Grant method. It declares authorization
to the grantee on behalf of the granter with the provided expiration time. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L36
\* @typeAlias: MSG_GRANT = [grant: GRANT, grantee: ADDRESS, granter: ADDRESS, type: Str];
\* @type: Set(MSG_GRANT);
MsgGrant == [
    type: {"grant"},
    granter: Address,
    grantee: Address,
    grant: Grants
]

(******************************************************************************)
(* A grant can be removed with the MsgRevoke message. MsgRevoke revokes any
authorization with the provided sdk.Msg type on the granter's account with 
that has been granted to the grantee. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L196
\* @typeAlias: MSG_REVOKE = [grantee: ADDRESS, granter: ADDRESS, msgTypeUrl: MSG_TYPE_URL, type: Str];
\* @type: Set(MSG_REVOKE);
MsgRevoke == [
    type: {"revoke"},
    granter: Address,
    grantee: Address,
    msgTypeUrl: MsgTypeUrls
]

\* @type: (MSG_REVOKE) => GRANT_ID;
grantIdOfMsgRevoke(msg) == [
    grantee |-> msg.grantee,
    granter |-> msg.granter,
    msgTypeUrl |-> msg.msgTypeUrl
]

(******************************************************************************)
(* Messages to be executed, such as Send messages or Stake messages. The content
of a message depends on the implementation of the authorization logic. A signer
of the message corresponds to the granter of the authorization. A message
implements an Authorization interface (methods MsgTypeURL and Accept). *)
(******************************************************************************)
\* @typeAlias: SDK_MSG = [signer: ADDRESS, content: SDK_MSG_CONTENT];
\* @type: Set(SDK_MSG);
SdkMsgs == [signer: Address, content: SdkMsgContent]

(******************************************************************************)
(* MsgExec attempts to execute the provided messages using authorizations
granted to the grantee. Each message should have only one signer corresponding
to the granter of the authorization. *)
(******************************************************************************)
\* https://github.com/cosmos/cosmos-sdk/blob/3a1027c74b15ad78270dbe68b777280bde393576/x/authz/tx.pb.go#L116
\* @typeAlias: MSG_EXEC = [grantee: ADDRESS, msg: SDK_MSG, type: Str];
\* @type: Set(MSG_EXEC);
MsgExec == [
    type: {"exec"},

    grantee: Address,

	\* Each message must implement an Authorization interface. The x/authz module
	\* will try to find a grant matching (msg.signers[0], grantee, MsgTypeURL(msg))
	\* triple and validate it.
    msg: SdkMsgs
]

\* @typeAlias: EVENT = [g: GRANT_ID, type: Str];
\* @type: Set(EVENT);
ExpireEvents == [type: {"expire"}, g: ValidGrantIds]

\* @typeAlias: REQUEST_MSG = [grant: GRANT, grantee: ADDRESS, granter: ADDRESS, msgTypeUrl: MSG_TYPE_URL, msgs: Set(SDK_MSG), type: Str];
\* @type: Set(REQUEST_MSG);
RequestMessages == MsgGrant \cup MsgRevoke \cup MsgExec

--------------------------------------------------------------------------------
(******************************************************************************)
(* Responses *)
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
    type: {"grant"}, 
    ok: BOOLEAN, 
    error: MsgGrantResponseErrors
]

MsgExecResponseErrors == {
    "none", 
    "grant-not-found", 
    "authorization-expired", 
    \* From SendAuthorization:
    "insufficient-amount",
    \* From StakeAuthorization:
    "validator-not-allowed",
    "validator-denied"
}

\* @typeAlias: RESPONSE_EXEC = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_EXEC);
MsgExecResponses == [
    type: {"exec"}, 
    ok: BOOLEAN, 
    error: MsgExecResponseErrors
]

\* @typeAlias: RESPONSE_REVOKE = [ok: Bool, type: Str];
\* @type: Set(RESPONSE_REVOKE);
MsgRevokeResponses == [
    type: {"MsgRevokeResponses"}, 
    ok: BOOLEAN
]

\* @typeAlias: RESPONSE_MSG = [error: Str, ok: Bool, type: Str];
\* @type: Set(RESPONSE_MSG);
Responses == MsgGrantResponses \cup MsgExecResponses \cup MsgRevokeResponses

================================================================================
Created by Hernán Vanzetto on 10 August 2022
