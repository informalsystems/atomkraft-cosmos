---------------------------- MODULE AuthzSend ----------------------------------
(******************************************************************************)
(* SendAuthorization implements the Authorization interface for the
cosmos.bank.v1beta1.MsgSend Msg. It takes a SpendLimit that specifies the
maximum amount of tokens the grantee can spend. The SpendLimit is updated as the
tokens are spent. *)
(******************************************************************************)
EXTENDS Authz, Integers

Coins == Int

SendMsgTypeURL == "send"

\* Types of messages allowed to be granted permission
AuthorizationTypes == { SendMsgTypeURL }

\* SendAuthorization allows the grantee to spend up to spendLimit coins from
\* the granter's account.
\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/authz.pb.go#L33
SendAuthorization == [  
    type: {"SendAuthorization"},

	spendLimit: Coins,

	\* Specifies an optional list of addresses to whom the grantee can send
	\* tokens on behalf of the granter. If omitted, any recipient is allowed.
    allowList: SUBSET Address
]

UpdateSpendLimit(auth, spendLimit) == [
    type |-> "SendAuthorization",
    spendLimit |-> spendLimit,
    allowList |-> auth.toAddress
]

\* MsgSend represents a message to send coins from one account to another.
MsgSend == [
    type: {"MsgSend"},
	fromAddress: Address,
	toAddress: Address,
	amount: Coins
}

\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/send_authorization.go#L27
MsgTypeURL(auth) ==
    SendMsgTypeURL

\* https://github.com/cosmos/cosmos-sdk/blob/9f5ee97889bb2b4c8e54b9a81b13cd42f6115993/x/bank/types/send_authorization.go#L32
\* @type: SEND_MSG => ACCEPT_RESPONSE;
Accept(auth, msg) == 
    LET amount == msg.content.amount IN
    IF msg.content.validatorAddress \notin auth.allowList THEN
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> "validator-not-allowed"]
    ELSE IF amount < auth.spendLimit THEN
        [accept |-> FALSE, delete |-> FALSE, updated |-> auth, error |-> "insufficient-amount"]
    ELSE [
        accept |-> amount >= auth.spendLimit,
        delete |-> amount = auth.spendLimit,
        updated |-> IF amount > auth.spendLimit
                THEN UpdateSpendLimit(auth, auth.spendLimit - amount)
                ELSE NoAuthorization,
        error |-> "none"
    ]

INSTANCE Authz WITH 
    MsgTypeUrls <- AuthorizationTypes,
    Authorization <- SendAuthorization,
    SdkMsgContent <- MsgSend,
    MsgTypeURL <- MsgTypeURL,
    Accept <- Accept

================================================================================