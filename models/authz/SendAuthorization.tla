------------------------- MODULE SendAuthorization -----------------------------
(******************************************************************************)
(* SendAuthorization implements the Authorization interface for the
cosmos.bank.v1beta1.MsgSend Msg. It takes a SpendLimit that specifies the
maximum amount of tokens the grantee can spend. The SpendLimit is updated as the
tokens are spent. *)
(******************************************************************************)
LOCAL INSTANCE MsgTypes
LOCAL INSTANCE Integers

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
\* @typeAlias: SDK_MSG = [signer: ACCOUNT, amount: COINS, fromAddress: ACCOUNT, toAddress: ACCOUNT, typeUrl: MSG_TYPE_URL];
\* @type: Set(SDK_MSG);
MsgSend ==
    LET Msgs == [
        signer: Accounts, 
        typeUrl: MsgTypeUrls,
        fromAddress: Accounts,
        toAddress: Accounts,
        amount: Coins
    ] IN 
    { msg \in Msgs: msg.fromAddress # msg.toAddress /\ msg.amount > 0 }

--------------------------------------------------------------------------------
\* Authorization that allows the grantee to spend up to spendLimit coins from
\* the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/authz.pb.go#L33
\* @typeAlias: AUTH = [msgTypeUrl: MSG_TYPE_URL, spendLimit: COINS];
\* @type: Set(AUTH);
Authorization == [
    type: {"send-authorization"},
    
    \* Terra SDK: "spend limit must be positive" (error code=10)
    spendLimit: { c \in Coins : c > 0 },
    
    \* Specifies an optional list of addresses to whom the grantee can send
    \* tokens on behalf of the granter. If omitted, any recipient is allowed.
    \* Since cosmos-sdk 0.47
    allowList: SUBSET Accounts,

    msgTypeUrl: MsgTypeUrls \* Not present in the code.
]

\* Apalache does not like the expression:
\*      [auth EXCEPT !.spendLimit = auth.spendLimit - amount]
\* @type: (AUTH, COINS) => AUTH;
UpdateSpendLimit(auth, spendLimit) == [
    type |-> "stake-authorization",
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
    IN
    IF auth.allowList # {} /\ msg.toAddress \notin auth.allowList THEN
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> "account-not-allowed"]
    ELSE IF amount = 0 THEN 
        [ accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> "invalid-request" ]
    ELSE [
        accept |-> amount <= auth.spendLimit,
        delete |-> amount = auth.spendLimit,
        updated |-> IF amount < auth.spendLimit
            \* UpdateSpendLimit(auth, auth.spendLimit - amount)
            THEN [
                    type |-> "stake-authorization",
                    spendLimit |-> auth.spendLimit - amount, 
                    allowList |-> auth.allowList, 
                    msgTypeUrl |-> auth.msgTypeUrl
                ]
            ELSE auth,
        error |-> IF amount <= auth.spendLimit THEN "none" ELSE "insufficient-amount"
    ]

================================================================================
Created by Hernán Vanzetto on 10 August 2022
