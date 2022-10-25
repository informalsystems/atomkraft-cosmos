-------------------------------- MODULE Grants ---------------------------------
(******************************************************************************)

(******************************************************************************)
CONSTANTS
    \* @typeAlias: ACCOUNT = Str;
    \* @type: Set(ACCOUNT);
    Accounts,

    \* @typeAlias: VALIDATOR = Str;
    \* @type: Set(VALIDATOR);
    Validators
--------------------------------------------------------------------------------
CONSTANTS 
    \* @typeAlias: COINS = Int;
    \* @type: Set(COINS);
    Coins,
    \* @type: COINS;
    NoMaxCoins

--------------------------------------------------------------------------------
Generic == INSTANCE GenericAuthorization
Send == INSTANCE SendAuthorization
Stake == INSTANCE StakeAuthorization

MsgTypeUrls == 
    Generic!MsgTypeUrls \cup 
    Send!MsgTypeUrls \cup 
    Stake!MsgTypeUrls

MsgTypeURL(auth) ==
    CASE auth.type = "generic-authorization" -> 
        Generic!MsgTypeURL(auth)
      [] auth.type = "send-authorization" -> 
        Send!MsgTypeURL(auth)
      [] auth.type = "stake-authorization" -> 
        Stake!MsgTypeURL(auth)

Accept(auth, msg) ==
    CASE auth.type = "generic-authorization" -> 
        Generic!Accept(auth, msg)
      [] auth.type = "send-authorization" -> 
        Send!Accept(auth, msg)
      [] auth.type = "stake-authorization" -> 
        Stake!Accept(auth, msg)

--------------------------------------------------------------------------------
\* @typeAlias: AUTH = [maxTokens: COINS, validators: Set(VALIDATOR), allow: Bool, msgTypeUrl: MSG_TYPE_URL, spendLimit: COINS, allowList: Set(ACCOUNT), type: Str];
\* @type: Set(AUTH);
Authorization == 
    Generic!Authorization \cup 
    Send!Authorization \cup 
    Stake!Authorization

AuthValidateBasic(auth) ==
    CASE auth.type = "generic-authorization" -> 
        Generic!AuthValidateBasic(auth)
      [] auth.type = "send-authorization" -> 
        Send!AuthValidateBasic(auth)
      [] auth.type = "stake-authorization" -> 
        Stake!AuthValidateBasic(auth)

--------------------------------------------------------------------------------
(******************************************************************************)
(* Messages to be executed, such as Send messages or Stake messages. The content
of a message depends on the implementation of the authorization logic. A signer
of the message corresponds to the granter of the authorization. An SDK message
may contain multiple signers, but authz accepts messages with just one.  A
message implements an Authorization interface (methods MsgTypeURL and 
Accept). *)
(******************************************************************************)
\* @typeAlias: SDK_MSG = [amount: COINS, delegatorAddress: ACCOUNT, fromAddress: ACCOUNT, toAddress: ACCOUNT, typeUrl: MSG_TYPE_URL, validatorAddress: VALIDATOR, validatorSrcAddress: VALIDATOR, validatorDstAddress: VALIDATOR];
\* @type: Set(SDK_MSG);
SdkMsg ==
    Send!MsgSend \cup 
    Stake!MsgDelegate \cup 
    Stake!MsgUndelegate \cup 
    Stake!MsgBeginRedelegate

SdkMsgValidateBasic(msg) ==
    CASE msg.typeUrl \in Send!MsgTypeUrls -> 
        Send!SdkMsgValidateBasic(msg)
      [] msg.typeUrl \in Stake!MsgTypeUrls -> 
        Stake!SdkMsgValidateBasic(msg)

--------------------------------------------------------------------------------
(******************************************************************************)
(* A grant is an allowance to execute a Msg by the grantee on behalf of the
granter. Grants are identified by combining granter address (the address 
bytes of the granter), grantee address (the address bytes of the grantee) 
and Authorization type (its type URL). Hence we only allow one grant for 
the (granter, grantee, Authorization) triple. *)
(******************************************************************************)
\* @typeAlias: GRANT_ID = [grantee: ACCOUNT, granter: ACCOUNT, msgTypeUrl: MSG_TYPE_URL];
\* @type: Set(GRANT_ID);
GrantIds == [
    granter: Accounts,
    grantee: Accounts,
    msgTypeUrl: MsgTypeUrls
]

\* Grant gives permissions to execute the provide method with expiration time.
\* https://github.com/cosmos/cosmos-sdk/blob/c1b6ace7d542925b526cf3eef6df38a206eab8d8/x/authz/authz.pb.go#L74
\* @typeAlias: GRANT = [authorization: AUTH, expiration: Str];
\* @type: Set(GRANT);
Grants == [
    authorization: Authorization,

    \* Time when the grant will expire with respect to the moment when the
    \* related event happens. If "none", then the grant doesn't have an 
    \* expiration time and other conditions in the authorization may apply to 
    \* invalidate it.
    expiration: {"past", "future", "none"}
]

\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/authorization_grant.go#L54
\* @type: (GRANT) => Str;
GrantValidateBasic(grant) ==
    AuthValidateBasic(grant.authorization)

\* @type: AUTH;
NoAuthorization == [ type |-> "NoAuthorization" ]

\* @type: GRANT;
NoGrant == [ authorization |-> NoAuthorization, expiration |-> "none" ]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
