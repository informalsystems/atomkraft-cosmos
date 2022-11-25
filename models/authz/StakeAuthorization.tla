------------------------ MODULE StakeAuthorization -----------------------------
(******************************************************************************)
(* StakeAuthorization implements the Authorization interface for messages in the
staking module. It takes an AuthorizationType to specify whether you want to
authorise delegating, undelegating or redelegating (i.e. these have to be
authorised seperately). It also takes a MaxTokens that keeps track of a limit to
the amount of tokens that can be delegated/undelegated/redelegated. If left
empty, the amount is unlimited. Additionally, this Msg takes an AllowList and a
DenyList, which allows you to select which validators you allow grantees to
stake with. *)
(******************************************************************************)
LOCAL INSTANCE Integers
LOCAL INSTANCE MsgTypes
LOCAL INSTANCE MsgErrors

CONSTANT
    \* @type: Set($account);
    Accounts,
    \* @type: Set($validator);
    Validators,
    \* @type: Set($coins);
    Coins,
    \* @type: $coins;
    NoMaxCoins

\* We want our model of Coins to include some negative number.
ASSUME \E min, max \in Int: 
    /\ min < 0
    /\ max > 0 
    /\ Coins = min .. max

\* @type: $coins;
ASSUME NoMaxCoins \in Int /\ NoMaxCoins \notin Coins

\* MsgDelegate defines a SDK message for performing a delegation of coins from a
\* delegator to a validator.
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/tx.pb.go#L205
\* @type: Set($sdkMsg);
MsgDelegate == [
    typeUrl: { DELEGATE_TYPE_URL },
    delegatorAddress: Accounts,
    validatorAddress: Validators,
    amount: Coins
]

\* MsgUndelegate defines a SDK message for performing an undelegation from a
\* delegate and a validator.
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/tx.pb.go#L419
\* @type: Set($sdkMsg);
MsgUndelegate == [
    typeUrl: { UNDELEGATE_TYPE_URL},
    delegatorAddress: Accounts,
    validatorAddress: Validators,
    amount: Coins
]

\* MsgBeginRedelegate defines a SDK message for performing a redelegation of
\* coins from a delegator and source validator to a destination validator.
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/tx.pb.go#L304
\* @type: Set($sdkMsg);
MsgBeginRedelegate == [
    typeUrl: { BEGIN_REDELEGATE_TYPE_URL },
    delegatorAddress: Accounts,
    validatorSrcAddress: Validators,
    validatorDstAddress: Validators,
    amount: Coins
]

\* Types of messages allowed to be granted permission
\* @type: Set($msgTypeUrl);
MsgTypeUrls == { m.typeUrl: m \in MsgDelegate \cup MsgUndelegate \cup MsgBeginRedelegate }

\* @type: ($sdkMsg) => Str;
SdkMsgValidateBasic(sdkMsg) == 
    CASE sdkMsg.typeUrl = DELEGATE_TYPE_URL ->
        \* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/msg.go#L227
        IF sdkMsg.amount < 0 /\ sdkMsg.amount # NoMaxCoins THEN 
            INVALID_DELEGATION_AMOUNT 
        ELSE IF sdkMsg.amount = 0 THEN 
            \* CHECK: It's possible to execute a message to delegate 0 tokens
            "none"
        ELSE 
            "none"
      [] sdkMsg.typeUrl \in {UNDELEGATE_TYPE_URL, BEGIN_REDELEGATE_TYPE_URL} ->
        \* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/msg.go#L329
        IF sdkMsg.amount < 0 /\ sdkMsg.amount # NoMaxCoins THEN 
            INVALID_SHARES_AMOUNT
        ELSE IF sdkMsg.amount = 0 THEN 
            \* CHECK: It's possible to execute a message to re/undelegate 0 tokens
            "none"
        ELSE 
            "none"
      [] OTHER ->
        "none"

--------------------------------------------------------------------------------
\* The authorization for delegate/undelegate/redelegate.
\* Issue for bug when deny list is not empty: https://github.com/cosmos/cosmos-sdk/issues/11391
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/authz.go#L16
\* @type: Set($auth);
Authorization == [  
    type: {"stake-authorization"},

    \* Specifies the maximum amount of tokens can be delegate to a validator. If
    \* it is empty, there is no spend limit and any amount of coins can be
    \* delegated.
    maxTokens: Coins \cup {NoMaxCoins},

    \* A set of validator addresses to whom delegation of tokens is either
    \* allowed or denied.
    validators: SUBSET Validators \ {{}},

    \* Extra field not present in the code.
    \* If TRUE, validators is a list of allowed addresses. 
    \* If FALSE, validators is a list of address that should not be granted delegation.
    allow: BOOLEAN,

    \* Specifies one of three authorization types.
    msgTypeUrl: MsgTypeUrls
]

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/authz.go#L46
\* @type: ($auth) => Str;
AuthValidateBasic(auth) ==
    IF auth.maxTokens < 0 /\ auth.maxTokens # NoMaxCoins THEN
        NEGATIVE_COIN_AMOUNT
    ELSE IF auth.maxTokens = 0 THEN
        \* CHECK: It's possible to request authorization to re/un/delegate 0 tokens
        "none"
    ELSE
        "none"

\* Apalache does not like the expression:
\*      [auth EXCEPT !.maxTokens = auth.maxTokens - amount]
\* Error message:         
\*     The specification is malformed: An updated record has more fields than its
\*     declared type: A record with the inferred type `[allow: Bool,
\*     msgTypeUrl: Str, maxTokens: Int, type: Str, validators: Set(Str)]`
\*     has been updated with the key `validators` in an `EXCEPT` expression and the
\*     updated record has more fields than are specified in its type annotation.
\*     For details see
\*     https://apalache.informal.systems/docs/apalache/known-issues.html#updating-records-with-excess-fields
\* @type: ($auth, $coins) => $auth;
UpdateMaxTokens(auth, maxTokens) == [
    type |-> "stake-authorization",
    maxTokens |-> maxTokens, 
    validators |-> auth.validators, 
    allow |-> auth.allow, 
    msgTypeUrl |-> auth.msgTypeUrl
]

--------------------------------------------------------------------------------
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/authz.go#L38
\* @type: ($auth) => $msgTypeUrl;
MsgTypeURL(auth) ==
    auth.msgTypeUrl

\* @type: ($sdkMsg) => $validator;
ValidatorAddressOf(msg) ==
    CASE msg.typeUrl = DELEGATE_TYPE_URL -> msg.validatorAddress 
      [] msg.typeUrl = UNDELEGATE_TYPE_URL -> msg.validatorAddress 
      [] msg.typeUrl = BEGIN_REDELEGATE_TYPE_URL -> msg.validatorDstAddress 

\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/staking/types/authz.go#L58
\* @typeAlias: acceptResponse = {accept: Bool, delete: Bool, updated: $auth, error: Str};
\* @type: ($auth, $sdkMsg) => $acceptResponse;
Accept(auth, msg) == 
    LET 
        \* @type: $validator;
        validatorAddress == ValidatorAddressOf(msg)
    IN

    \* The error messages for when a validator does not belong to the allowed
    \* list or does belong to the deny list are the same, and this could hide some
    \* potential problems.
    CASE auth.allow /\ validatorAddress \notin auth.validators ->
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> CANNOT_DELEGATE_TO_VALIDATOR]
      [] ~ auth.allow /\ validatorAddress \in auth.validators ->
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> CANNOT_DELEGATE_TO_VALIDATOR]
      [] auth.maxTokens = NoMaxCoins ->
        [accept |-> TRUE, delete |-> FALSE, updated |-> auth, error |-> "none"]
      [] OTHER -> [ 
            accept |-> msg.amount <= auth.maxTokens, 
            delete |-> msg.amount = auth.maxTokens, 
            updated |-> IF msg.amount < auth.maxTokens
                THEN UpdateMaxTokens(auth, auth.maxTokens - msg.amount)
                ELSE auth,
            error |-> IF msg.amount <= auth.maxTokens THEN "none" ELSE NEGATIVE_COIN_AMOUNT
        ]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
