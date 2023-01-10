------------------------- MODULE CosmosBaseV1beta1Coin -------------------------
\* package: cosmos.base.v1beta1

CONSTANT
    DENOM

\* Coin defines a token with a denomination and an amount.
\*
\* NOTE: The amount field is an Int which implements the custom method
\* signatures required by gogoproto.
Coin == [ 
    _tag_: {"coin"},

    \* label: optional
    denom: DENOM,

    \* label: optional
    amount: CoinAmount
]

\* DecCoin defines a token with a denomination and a decimal amount.
\*
\* NOTE: The amount field is an Dec which implements the custom method
\* signatures required by gogoproto.
DecCoin == [ 
    _tag_: {"dec-coin"},

    \* label: optional
    denom: DENOM,

    \* label: optional
    amount: CoinAmount
]

\* IntProto defines a Protobuf wrapper around an Int object.
IntProto == [ 
    _tag_: {"int-proto"},

    \* label: optional
    int: STRING
]

\* DecProto defines a Protobuf wrapper around a Dec object.
DecProto == [ 
    _tag_: {"dec-proto"},

    \* label: optional
    dec: STRING
]

================================================================================
File automatically generated from cosmos/base/v1beta1/coin.proto on 2022-11-18 14:11:54 CET
