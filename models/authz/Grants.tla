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
    CASE auth.msgTypeUrl \in Generic!MsgTypeUrls -> 
        Generic!MsgTypeURL(auth)
      [] auth.msgTypeUrl \in Send!MsgTypeUrls -> 
        Send!MsgTypeURL(auth)
      [] auth.msgTypeUrl \in Stake!MsgTypeUrls -> 
        Stake!MsgTypeURL(auth)

Accept(auth, msg) ==
    CASE msg.typeUrl \in Generic!MsgTypeUrls -> 
        Generic!Accept(auth, msg)
      [] msg.typeUrl \in Send!MsgTypeUrls -> 
        Send!Accept(auth, msg)
      [] msg.typeUrl \in Stake!MsgTypeUrls -> 
        Stake!Accept(auth, msg)

--------------------------------------------------------------------------------
\* @typeAlias: AUTH = [maxTokens: COINS, validators: Set(VALIDATOR), allow: Bool, msgTypeUrl: MSG_TYPE_URL, spendLimit: COINS, allowList: Set(ACCOUNT), type: Str];
\* @type: Set(AUTH);
Authorization == 
    Generic!Authorization \cup 
    Send!Authorization \cup 
    Stake!Authorization

--------------------------------------------------------------------------------
(******************************************************************************)
(* Messages to be executed, such as Send messages or Stake messages. The content
of a message depends on the implementation of the authorization logic. A signer
of the message corresponds to the granter of the authorization. An SDK message
may contain multiple signers, but authz accepts messages with just one.  A
message implements an Authorization interface (methods MsgTypeURL and 
Accept). *)
(******************************************************************************)
\* @typeAlias: SDK_MSG = [amount: COINS, delegatorAddress: ACCOUNT, fromAddress: ACCOUNT, signer: ACCOUNT, toAddress: ACCOUNT, typeUrl: MSG_TYPE_URL, validatorAddress: VALIDATOR, validatorSrcAddress: VALIDATOR, validatorDstAddress: VALIDATOR];
\* @type: Set(SDK_MSG);
SdkMsg ==
    Send!MsgSend \cup 
    Stake!MsgDelegate \cup 
    Stake!MsgUndelegate \cup 
    Stake!MsgBeginRedelegate

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

\* @type: (GRANT_ID) => Bool;
IsValid(grantId) == grantId.granter # grantId.grantee

\* @type: Set(GRANT_ID);
ValidGrantIds == { g \in GrantIds: IsValid(g) }

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

\* @type: AUTH;
NoAuthorization == [ type |-> "NoAuthorization" ]

\* @type: GRANT;
NoGrant == [ authorization |-> NoAuthorization, expiration |-> "none" ]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
