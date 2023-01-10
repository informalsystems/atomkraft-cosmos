--------------------------- MODULE CosmosGovV1Model ---------------------------
\* package: cosmos.authz.v1beta1
EXTENDS Integers, Coins

\* Account addresses.
\* @typeAlias: address = Str;
\* @type: Set($address);
Address == { 
    "a1",

    "a2",

    "a3"
}

\* @typeAlias: timestamp = Str;
\* @type: $timestamp;
NoTimestamp == "TS_NONE"

\* @type: Set($timestamp);
Timestamp == { 
    "TS_NOW",
    
    "TS_NOW_PLUS_DEPOSIT_PERIOD_PARAM",

    NoTimestamp
}

\* @typeAlias: duration = Str;
\* @type: Set($duration);
Duration == { 
    "DUR_0",

    "DUR_1"
}

\* @typeAlias: proposalId = Int;
\* @type: Set($proposalId);
ProposalId == {-1, 0, 1, 2}

\* @typeAlias: percentage = Int;
\* @type: Set($percentage);
\* Percentage == 0 .. 100
Percentage == {0, 50, 100}

================================================================================
File automatically generated from cosmos/gov/v1/model.proto on 2022-11-18 14:11:54 CET
