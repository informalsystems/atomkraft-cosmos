-------------------------------- MODULE SdkMsgs --------------------------------
EXTENDS 
    CosmosGovV1Model
    \* CosmosBaseV1beta1Coin

--------------------------------------------------------------------------------
\* @typeAlias: msgTypeUrl = Str;
\* @type: $msgTypeUrl;
SEND_TYPE_URL == "send"

\* The message to send coins from one account to another.
\* https://github.com/cosmos/cosmos-sdk/blob/6d32debf1aca4b7f1ed1429d87be1d02c315f02d/x/bank/types/tx.pb.go#L36
\* @typeAlias: sdkMsg = [typeUrl: $msgTypeUrl, fromAddress: $address, toAddress: $address, amount: $coin];
\* @type: Set($sdkMsg);
MsgSend == [
    typeUrl: { SEND_TYPE_URL },
    fromAddress: Address,
    toAddress: Address,
    amount: Coin
]


\* @type: $sdkMsg;
NoMessage == [
    typeUrl |-> "no-message"
]

SdkMsg ==
    MsgSend \cup {NoMessage}

================================================================================
