------------------------- MODULE SendAuthorization -----------------------------
(******************************************************************************)
(* SendAuthorization implements the Authorization interface for the
cosmos.bank.v1beta1.MsgSend Msg. It takes a SpendLimit that specifies the
maximum amount of tokens the grantee can spend. The SpendLimit is updated as the
tokens are spent. *)
(******************************************************************************)
LOCAL INSTANCE Integers
LOCAL INSTANCE MsgTypes
LOCAL INSTANCE MsgErrors

CONSTANT
    \* @typeAlias: ACCOUNT = Str;
    \* @type: Set(ACCOUNT);
    Accounts, 
    \* @typeAlias: COINS = Int;
    \* @type: Set(COINS);
    Coins

\* We want our model of Coins to include some negative number.
ASSUME \E min, max \in Int: 
    /\ min < 0
    /\ max > 0 
    /\ Coins = min .. max

\* Types of messages allowed to be granted permission
\* @type: Set(MSG_TYPE_URL);
MsgTypeUrls == { SEND_TYPE_URL }

\* The message to send coins from one account to another.
\* https://github.com/cosmos/cosmos-sdk/blob/5019459b1b2028119c6ca1d80714caa7858c2076/x/bank/types/tx.pb.go#L36
\* @type: Set(SDK_MSG);
MsgSend == [
    typeUrl: MsgTypeUrls,
    fromAddress: Accounts,
    toAddress: Accounts,
    amount: Coins
]

\* @type: (SDK_MSG) => Str;
SdkMsgValidateBasic(sdkMsg) == 
    \* https://github.com/cosmos/cosmos-sdk/blob/25e7f9bee2b35f0211b0e323dd062b55bef987b7/x/bank/types/msgs.go#L30
    IF sdkMsg.amount <= 0 THEN 
        INVALID_COINS
        \* SPEND_LIMIT_MUST_BE_POSITIVE 
    ELSE 
        "none"

--------------------------------------------------------------------------------
\* Authorization that allows the grantee to spend up to spendLimit coins from
\* the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/authz.pb.go#L33
\* @typeAlias: AUTH = [msgTypeUrl: MSG_TYPE_URL, spendLimit: COINS, allowList: Set(ACCOUNT), type: Str];
\* @type: Set(AUTH);
Authorization == [
    type: {"send-authorization"},
    
    spendLimit: Coins,
    
    \* Specifies an optional list of addresses to whom the grantee can send
    \* tokens on behalf of the granter. If omitted, any recipient is allowed.
    \* Since cosmos-sdk 0.47
    allowList: SUBSET Accounts,

    msgTypeUrl: MsgTypeUrls \* Not present in the code.
]

\* @type: (AUTH) => Str;
AuthValidateBasic(auth) ==
    IF auth.spendLimit <= 0 THEN
        SPEND_LIMIT_MUST_BE_POSITIVE
    ELSE
        "none"

\* Apalache does not like the expression:
\*      [auth EXCEPT !.spendLimit = auth.spendLimit - amount]
\* @type: (AUTH, COINS) => AUTH;
UpdateSpendLimit(auth, spendLimit) == [
    type |-> "send-authorization",
    spendLimit |-> spendLimit, 
    allowList |-> auth.allowList, 
    msgTypeUrl |-> auth.msgTypeUrl
]

--------------------------------------------------------------------------------
\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/send_authorization.go#L27
\* @type: (AUTH) => MSG_TYPE_URL;
MsgTypeURL(auth) == 
    auth.msgTypeUrl

\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/send_authorization.go#L32
\* @typeAlias: ACCEPT_RESPONSE = [accept: Bool, delete: Bool, updated: AUTH, error: Str];
\* @type: (AUTH, SDK_MSG) => ACCEPT_RESPONSE;
Accept(auth, msg) == 
    LET 
        \* @type: COINS;
        amount == msg.amount
        \* @type: Bool;
        isAllowed == msg.toAddress \in auth.allowList
    IN
    CASE msg.toAddress \notin auth.allowList ->
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> ADDRESS_NOT_ALLOWED]
      [] amount = 0 ->
        \* CHECK: unreachable?
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> SPEND_LIMIT_IS_NIL]
      [] amount < 0 ->
        \* CHECK: unreachable?
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> SPEND_LIMIT_IS_NEGATIVE]
      [] msg.amount > auth.spendLimit ->
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> INSUFFICIENT_AMOUNT]
      [] OTHER -> [
            accept |-> TRUE,
            delete |-> msg.amount = auth.spendLimit,
            updated |-> [ 
                type |-> "send-authorization",
                spendLimit |-> auth.spendLimit - msg.amount, 
                allowList |-> auth.allowList, 
                msgTypeUrl |-> auth.msgTypeUrl
            ], \* UpdateSpendLimit(auth, auth.spendLimit - msg.amount)
            error |-> "none"
        ]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
