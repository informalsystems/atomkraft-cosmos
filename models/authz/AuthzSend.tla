---------------------------- MODULE AuthzSend ----------------------------------
(******************************************************************************)
(* SendAuthorization implements the Authorization interface for the
cosmos.bank.v1beta1.MsgSend Msg. It takes a SpendLimit that specifies the
maximum amount of tokens the grantee can spend. The SpendLimit is updated as the
tokens are spent. *)
(******************************************************************************)
EXTENDS AuthzBase, Integers

CONSTANT
    \* @typeAlias: COINS = Int;
    \* @type: Set(COINS);
    Coins

ASSUME Coins \in SUBSET Int

\* @typeAlias: MSG_TYPE_URL = Str;
\* @type: MSG_TYPE_URL;
SendMsgTypeURL == "send"

\* The message to send coins from one account to another.
\* https://github.com/cosmos/cosmos-sdk/blob/5019459b1b2028119c6ca1d80714caa7858c2076/x/bank/types/tx.pb.go#L36
\* @typeAlias: SDK_MSG_CONTENT = [amount: COINS, fromAddress: ADDRESS, toAddress: ADDRESS, type: MSG_TYPE_URL];
\* @type: Set(SDK_MSG_CONTENT);
SdkMsgContent == 
    LET Msgs == [
        type: {"MsgSend"},
        fromAddress: Address,
        toAddress: Address,
        amount: Coins
    ] IN 
    { msg \in Msgs: msg.fromAddress # msg.toAddress /\ msg.amount > 0 }

\* Types of messages allowed to be granted permission
\* @type: Set(MSG_TYPE_URL);
MsgTypeUrls == { SendMsgTypeURL }

--------------------------------------------------------------------------------

\* SendAuthorization allows the grantee to spend up to spendLimit coins from
\* the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/authz.pb.go#L33
\* @type: AUTH;
Authorization == [  
    type: {"SendAuthorization"},

	spendLimit: Coins
]

\* @type: AUTH;
NoAuthorization == [ type |-> "NoAuthorization" ]

--------------------------------------------------------------------------------

\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/send_authorization.go#L27
MsgTypeURL(auth) ==
    SendMsgTypeURL

\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/send_authorization.go#L32
\* @type: SEND_MSG => ACCEPT_RESPONSE;
Accept(auth, msg) == 
    LET amount == msg.content.amount IN
    IF amount < auth.spendLimit THEN
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> "insufficient-amount"]
    ELSE [
        accept |-> amount >= auth.spendLimit,
        delete |-> amount <= auth.spendLimit,
        updated |-> IF amount > auth.spendLimit
            THEN [ type |-> "SendAuthorization", spendLimit |-> auth.spendLimit - amount]
            ELSE NoAuthorization,
        error |-> "none"
    ]

--------------------------------------------------------------------------------

\* INSTANCE Authz WITH 
\*     MsgTypeUrls <- MsgTypeUrls,
\*     SdkMsgContent <- SdkMsgContent,
\*     Authorization <- Authorization,
\*     MsgTypeURL <- MsgTypeURL,
\*     Accept <- Accept

================================================================================
Created by Hernán Vanzetto on 10 August 2022
