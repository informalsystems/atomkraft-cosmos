------------------------- MODULE CosmosBaseV1beta1Coin -------------------------
\* package: cosmos.base.v1beta1

\* Coin defines a token with a denomination and an amount.
\*
\* NOTE: The amount field is an Int which implements the custom method
\* signatures required by gogoproto.
Coin == [ 
    msgType: {"coin"},

    \* label: optional
    denom: STRING,

    \* label: optional
    amount: STRING
]

\* DecCoin defines a token with a denomination and a decimal amount.
\*
\* NOTE: The amount field is an Dec which implements the custom method
\* signatures required by gogoproto.
DecCoin == [ 
    msgType: {"dec-coin"},

    \* label: optional
    denom: STRING,

    \* label: optional
    amount: STRING
]

\* IntProto defines a Protobuf wrapper around an Int object.
IntProto == [ 
    msgType: {"int-proto"},

    \* label: optional
    int: STRING
]

\* DecProto defines a Protobuf wrapper around a Dec object.
DecProto == [ 
    msgType: {"dec-proto"},

    \* label: optional
    dec: STRING
]

================================================================================
File automatically generated from cosmos/base/v1beta1/coin.proto on 2022-11-18 14:11:54 CET
