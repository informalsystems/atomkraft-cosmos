---------------------------- MODULE CosmosGovV1Gov ----------------------------
\* package: cosmos.gov.v1

EXTENDS
    \* Reals,
    Integers,
    \* Sequences,
    SdkMsgs,
    \* CosmosBaseV1beta1Coin,
    CosmosGovV1Model
    
\* CONSTANTS
\*     SdkMsg

\* VoteOption enumerates the valid vote options for a given governance proposal.
\* @typeAlias: voteOption = Str;
\* @type: Set($voteOption);
VoteOption == { 
    \* VOTE_OPTION_UNSPECIFIED defines a no-op vote option.
    "VOTE_OPTION_UNSPECIFIED",

    \* VOTE_OPTION_YES defines a yes vote option.
    "VOTE_OPTION_YES",

    \* VOTE_OPTION_ABSTAIN defines an abstain vote option.
    "VOTE_OPTION_ABSTAIN",

    \* VOTE_OPTION_NO defines a no vote option.
    "VOTE_OPTION_NO",

    \* VOTE_OPTION_NO_WITH_VETO defines a no with veto vote option.
    "VOTE_OPTION_NO_WITH_VETO"
}

\* ProposalStatus enumerates the valid statuses of a proposal.
\* @typeAlias: proposalStatus = Str;
\* @type: Set($proposalStatus);
ProposalStatus == { 
    \* PROPOSAL_STATUS_UNSPECIFIED defines the default proposal status.
    "PROPOSAL_STATUS_UNSPECIFIED",

    \* PROPOSAL_STATUS_DEPOSIT_PERIOD defines a proposal status during the deposit
    \* period.
    "PROPOSAL_STATUS_DEPOSIT_PERIOD",

    \* PROPOSAL_STATUS_VOTING_PERIOD defines a proposal status during the voting
    \* period.
    "PROPOSAL_STATUS_VOTING_PERIOD",

    \* PROPOSAL_STATUS_PASSED defines a proposal status of a proposal that has
    \* passed.
    "PROPOSAL_STATUS_PASSED",

    \* PROPOSAL_STATUS_REJECTED defines a proposal status of a proposal that has
    \* been rejected.
    "PROPOSAL_STATUS_REJECTED",

    \* PROPOSAL_STATUS_FAILED defines a proposal status of a proposal that has
    \* failed.
    "PROPOSAL_STATUS_FAILED"
}

--------------------------------------------------------------------------------
\* WeightedVoteOption defines a unit of vote for vote split.
\* @typeAlias: weightedVoteOption = [_tag_: Str, option: $voteOption, weight: $percentage];
\* @type: Set($weightedVoteOption);
WeightedVoteOption == [ 
    _tag_: {"weighted-vote-option"},

    \* label: optional
    option: VoteOption,

    \* label: optional
    weight: Percentage
]

\* Deposit defines an amount deposited by an account address to an active
\* proposal.
\* @typeAlias: deposit = [_tag_: Str, proposalId: $proposalId, depositor: $address, amount: $coins];
\* @type: Set($deposit);
Deposit == [ 
    _tag_: {"deposit"},

    \* label: optional
    proposalId: ProposalId,

    \* label: optional
    depositor: Address,

    \* label: repeated
    amount: Coins
]

\* TallyResult defines a standard tally for a governance proposal.
\* @typeAlias: tallyResult = [_tag_: Str, yesCount: Int, abstainCount: Int, noCount: Int, noWithVetoCount: Int];
\* @type: Set($tallyResult);
TallyResult == [ 
    _tag_: {"tally-result"},

    \* label: optional
    yesCount: Int,

    \* label: optional
    abstainCount: Int,

    \* label: optional
    noCount: Int,

    \* label: optional
    noWithVetoCount: Int
]

\* Proposal defines the core field members of a governance proposal.
\* @typeAlias: proposal = [_tag_: Str, id: $proposalId, message: $sdkMsg, status: $proposalStatus, finalTallyResult: $tallyResult, submitTime: $timestamp, depositEndTime: $timestamp, totalDeposit: $coins, votingStartTime: $timestamp, votingEndTime: $timestamp, metadata: Str];
\* @type: Set($proposal);
Proposal == [ 
    _tag_: {"proposal"},

    \* label: optional
    id: ProposalId,

    \* label: repeated
    \* messages: BSeq(SdkMsg),
    message: SdkMsg,

    \* label: optional
    status: ProposalStatus,

    \* final_tally_result is the final tally result of the proposal. When
    \* querying a proposal via gRPC, this field is not populated until the
    \* proposal's voting period has ended.
    \* label: optional
    finalTallyResult: TallyResult,

    \* label: optional
    submitTime: Timestamp,

    \* label: optional
    depositEndTime: Timestamp,

    \* label: repeated
    totalDeposit: Coins,

    \* label: optional
    votingStartTime: Timestamp,

    \* label: optional
    votingEndTime: Timestamp,

    \* metadata is any arbitrary metadata attached to the proposal.
    \* label: optional
    metadata: STRING
]

\* Vote defines a vote on a governance proposal.
\* A Vote consists of a proposal ID, the voter, and the vote option.
\* @typeAlias: vote = [_tag_: Str, proposalId: $proposalId, voter: $address, options: Set($weightedVoteOption), metadata: Str];
\* @type: Set($vote);
Vote == [ 
    _tag_: {"vote"},

    \* label: optional
    proposalId: ProposalId,

    \* label: optional
    voter: Address,

    \* label: repeated
    \* options: BSeq(WeightedVoteOption),
    options: SUBSET WeightedVoteOption,

    \* metadata is any  arbitrary metadata to attached to the vote.
    \* label: optional
    metadata: STRING
]

\* DepositParams defines the params for deposits on governance proposals.
\* @typeAlias: depositParams = [_tag_: Str, minDeposit: $coins, maxDepositPeriod: $duration];
\* @type: Set($depositParams);
DepositParams == [ 
    _tag_: {"deposit-params"},

    \* Minimum deposit for a proposal to enter voting period.
    \* label: repeated
    minDeposit: Coins,

    \* Maximum period for Atom holders to deposit on a proposal. Initial value: 2
    \*  months.
    \* label: optional
    maxDepositPeriod: Duration
]

\* VotingParams defines the params for voting on governance proposals.
\* @typeAlias: votingParams = [_tag_: Str, votingPeriod: $duration];
\* @type: Set($votingParams);
VotingParams == [ 
    _tag_: {"voting-params"},

    \* Length of the voting period.
    \* label: optional
    votingPeriod: Duration
]

\* TallyParams defines the params for tallying votes on governance proposals.
\* @typeAlias: tallyParams = [_tag_: Str, quorum: $percentage, threshold: $percentage, vetoThreshold: $percentage];
\* @type: Set($tallyParams);
TallyParams == [ 
    _tag_: {"tally-params"},

    \* Minimum percentage of total stake needed to vote for a result to be
    \*  considered valid.
    \* label: optional
    quorum: Percentage,

    \* Minimum proportion of Yes votes for proposal to pass. Default value: 0.5.
    \* label: optional
    threshold: Percentage,

    \* Minimum value of Veto votes to Total votes ratio for proposal to be
    \*  vetoed. Default value: 1/3.
    \* label: optional
    vetoThreshold: Percentage
]

\* Params defines the parameters for the x/gov module.
\*
\* Since: cosmos-sdk 0.47
\* @typeAlias: params = [_tag_: Str, minDeposit: $coins, maxDepositPeriod: $duration, votingPeriod: $duration, quorum: $percentage, threshold: $percentage, vetoThreshold: $percentage, minInitialDepositRatio: $percentage];
\* @type: Set($params);
Params == [ 
    _tag_: {"params"},

    \* Minimum deposit for a proposal to enter voting period.
    \* label: repeated
    minDeposit: Coins,

    \* Maximum period for Atom holders to deposit on a proposal. Initial value: 2
    \*  months.
    \* label: optional
    maxDepositPeriod: Duration,

    \* Length of the voting period.
    \* label: optional
    votingPeriod: Duration,

    \* Minimum percentage of total stake needed to vote for a result to be
    \*  considered valid.
    \* label: optional
    quorum: Percentage,

    \* Minimum proportion of Yes votes for proposal to pass. Default value: 0.5.
    \* label: optional
    threshold: Percentage,

    \* Minimum value of Veto votes to Total votes ratio for proposal to be
    \*  vetoed. Default value: 1/3.
    \* label: optional
    vetoThreshold: Percentage,

    \* The ratio representing the proportion of the deposit value that must be paid at proposal submission.
    \* label: optional
    minInitialDepositRatio: Percentage
]

================================================================================
File automatically generated from cosmos/gov/v1/gov.proto on 2022-11-18 14:11:54 CET
