-------------------------------- MODULE Grants ---------------------------------
(******************************************************************************)

(******************************************************************************)
CONSTANTS
    \* @typeAlias: account = Str;
    \* @type: Set($account);
    Accounts,

    \* @typeAlias: validator = Str;
    \* @type: Set($validator);
    Validators
--------------------------------------------------------------------------------
CONSTANTS 
    \* @typeAlias: coins = Int;
    \* @type: Set($coins);
    Coins,
    \* @type: $coins;
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
\* @typeAlias: auth = {maxTokens: $coins, validators: Set($validator), allow: Bool, msgTypeUrl: $msgTypeUrl, spendLimit: $coins, allowList: Set($account), type: Str};
\* @type: Set($auth);
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
\* @typeAlias: sdkMsg = {amount: $coins, delegatorAddress: $account, fromAddress: $account, toAddress: $account, typeUrl: $msgTypeUrl, validatorAddress: $validator, validatorSrcAddress: $validator, validatorDstAddress: $validator};
\* @type: Set($sdkMsg);
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
\* @typeAlias: grantId = {grantee: $account, granter: $account, msgTypeUrl: $msgTypeUrl};
\* @type: Set($grantId);
GrantIds == [
    granter: Accounts,
    grantee: Accounts,
    msgTypeUrl: MsgTypeUrls
]

\* Grant gives permissions to execute the provide method with expiration time.
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/authz.pb.go#L74
\* @typeAlias: grant = {authorization: $auth, expiration: Str};
\* @type: Set($grant);
Grants == [
    authorization: Authorization,

    \* Time when the grant will expire with respect to the moment when the
    \* related event happens. If "none", then the grant doesn't have an 
    \* expiration time and other conditions in the authorization may apply to 
    \* invalidate it.
    expiration: {"past", "future", "none"}
]

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/authz/authorization_grant.go#L54
\* @type: ($grant) => Str;
GrantValidateBasic(grant) ==
    AuthValidateBasic(grant.authorization)

\* @type: $auth;
NoAuthorization == [ type |-> "NoAuthorization" ]

\* @type: $grant;
NoGrant == [ authorization |-> NoAuthorization, expiration |-> "none" ]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
