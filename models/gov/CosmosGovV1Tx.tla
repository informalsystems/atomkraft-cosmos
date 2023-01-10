----------------------------- MODULE CosmosGovV1Tx -----------------------------
\* package: cosmos.gov.v1

EXTENDS
    Integers,
    \* Sequences,
    \* CosmosBaseV1beta1Coin,
    MsgErrors,
    CosmosGovV1Gov,
    CosmosGovV1Model

VARIABLES
    \* @typeAlias: request = [_tag_: Str, message: $sdkMsg, initialDeposit: $coins, proposer: $address, metadata: Str, proposalId: $proposalId, voter: $address, option: $voteOption, options: Set($weightedVoteOption), depositor: $address, amount: $coins];
    \* @type: $request;
    request,
    
    \* @typeAlias: response = [_tag_: Str, error: Str, proposalId: $proposalId];
    \* @type: $response;
    response
    
--------------------------------------------------------------------------------
\* MsgSubmitProposal defines an sdk.Msg type that supports submitting arbitrary
\* proposal Content.
\* @typeAlias: msgSubmitProposal = [_tag_: Str, message: $sdkMsg, initialDeposit: $coins, proposer: $address, metadata: Str];
\* @type: Set($msgSubmitProposal);
MsgSubmitProposal == [ 
    _tag_: {"msg-submit-proposal"},

    \* label: repeated
    \* messages: BSeq(SdkMsg),
    message: SdkMsg,

    \* label: repeated
    initialDeposit: Coins,

    \* label: optional
    proposer: Address,

    \* metadata is any arbitrary metadata attached to the proposal.
    \* label: optional
    metadata: STRING
]

\* MsgSubmitProposalResponse defines the Msg/SubmitProposal response type.
\* @typeAlias: msgSubmitProposalResponse = [_tag_: Str, error: Str, proposalId: $proposalId];
\* @type: Set($msgSubmitProposalResponse);
MsgSubmitProposalResponse == [ 
    _tag_: {"msg-submit-proposal-response"},

    error: Errors,

    \* label: optional
    proposalId: ProposalId
]

\* MsgExecLegacyContent is used to wrap the legacy content field into a message.
\* This ensures backwards compatibility with v1beta1.MsgSubmitProposal.
\* @typeAlias: msgExecLegacyContent = [_tag_: Str, content: $sdkMsg, authority: Str];
\* @type: Set($msgExecLegacyContent);
MsgExecLegacyContent == [ 
    _tag_: {"msg-exec-legacy-content"},

    \* content is the proposal's content.
    \* label: optional
    \* content: Content,
    \* content: BSeq(SdkMsg),
    content: SdkMsg,

    \* authority must be the gov module address.
    \* label: optional
    authority: STRING
]

\* MsgExecLegacyContentResponse defines the Msg/ExecLegacyContent response type.
\* @typeAlias: msgExecLegacyContentResponse = [_tag_: Str, error: Str];
\* @type: Set($msgExecLegacyContentResponse);
MsgExecLegacyContentResponse == [ 
    _tag_: {"msg-exec-legacy-content-response"},

    error: Errors
]

\* MsgVote defines a message to cast a vote.
\* @typeAlias: msgVote = [_tag_: Str, proposalId: $proposalId, voter: $address, option: $voteOption, metadata: Str];
\* @type: Set($msgVote);
MsgVote == [ 
    _tag_: {"msg-vote"},

    \* label: optional
    proposalId: ProposalId,

    \* label: optional
    voter: Address,

    \* label: optional
    option: VoteOption,

    \* label: optional
    metadata: STRING
]

\* MsgVoteResponse defines the Msg/Vote response type.
\* @typeAlias: msgVoteResponse = [_tag_: Str, error: Str];
\* @type: Set($msgVoteResponse);
MsgVoteResponse == [ 
    _tag_: {"msg-vote-response"},

    error: Errors
]

\* MsgVoteWeighted defines a message to cast a vote.
\* @typeAlias: msgVoteWeighted = [_tag_: Str, proposalId: $proposalId, voter: $address, options: Set($weightedVoteOption), metadata: Str];
\* @type: Set($msgVoteWeighted);
MsgVoteWeighted == [ 
    _tag_: {"msg-vote-weighted"},

    \* label: optional
    proposalId: ProposalId,

    \* label: optional
    voter: Address,

    \* label: repeated
    \* options: BSeq(WeightedVoteOption),
    options: SUBSET WeightedVoteOption,

    \* label: optional
    metadata: STRING
]

\* MsgVoteWeightedResponse defines the Msg/VoteWeighted response type.
\* @typeAlias: msgVoteWeightedResponse = [_tag_: Str, error: Str];
\* @type: Set($msgVoteWeightedResponse);
MsgVoteWeightedResponse == [ 
    _tag_: {"msg-vote-weighted-response"},

    error: Errors
]

\* MsgDeposit defines a message to submit a deposit to an existing proposal.
\* @typeAlias: msgDeposit = [_tag_: Str, proposalId: $proposalId, depositor: $address, amount: $coins];
\* @type: Set($msgDeposit);
MsgDeposit == [ 
    _tag_: {"msg-deposit"},

    \* label: optional
    proposalId: ProposalId,

    \* label: optional
    depositor: Address,

    \* label: repeated
    amount: Coins
]

\* MsgDepositResponse defines the Msg/Deposit response type.
\* @typeAlias: msgDepositResponse = [_tag_: Str, error: Str];
\* @type: Set($msgDepositResponse);
MsgDepositResponse == [ 
    _tag_: {"msg-deposit-response"},

    error: Errors
]

\* MsgUpdateParams is the Msg/UpdateParams request type.
\*
\* Since: cosmos-sdk 0.47
\* @typeAlias: msgUpdateParams = [_tag_: Str, authority: $address, params: $params];
\* @type: Set($msgUpdateParams);
MsgUpdateParams == [ 
    _tag_: {"msg-update-params"},

    \* authority is the address of the governance account.
    \* label: optional
    authority: Address,

    \* params defines the x/gov parameters to update.
    \*
    \* NOTE: All parameters must be supplied.
    \* label: optional
    params: Params
]

\* MsgUpdateParamsResponse defines the response structure for executing a
\* MsgUpdateParams message.
\*
\* Since: cosmos-sdk 0.47
\* @typeAlias: msgUpdateParamsResponse = [_tag_: Str, error: Str];
\* @type: Set($msgUpdateParamsResponse);
MsgUpdateParamsResponse == [ 
    _tag_: {"msg-update-params-response"},

    error: Errors
]

--------------------------------------------------------------------------------
\* SubmitProposal defines a method to create new proposal given a content.
SendSubmitProposal(msgSubmitProposal) == 
    CHOOSE x \in MsgSubmitProposalResponse: TRUE

\* ExecLegacyContent defines a Msg to be in included in a MsgSubmitProposal
\* to execute a legacy content-based proposal.
SendExecLegacyContent(msgExecLegacyContent) == 
    CHOOSE x \in MsgExecLegacyContentResponse: TRUE

\* Vote defines a method to add a vote on a specific proposal.
SendVote(msgVote) == 
    CHOOSE x \in MsgVoteResponse: TRUE

\* VoteWeighted defines a method to add a weighted vote on a specific proposal.
SendVoteWeighted(msgVoteWeighted) == 
    CHOOSE x \in MsgVoteWeightedResponse: TRUE

\* Deposit defines a method to add deposit on a specific proposal.
SendDeposit(msgDeposit) == 
    CHOOSE x \in MsgDepositResponse: TRUE

\* UpdateParams defines a governance operation for updating the x/gov module
\* parameters. The authority is defined in the keeper.
\*
\* Since: cosmos-sdk 0.47
SendUpdateParams(msgUpdateParams) == 
    CHOOSE x \in MsgUpdateParamsResponse: TRUE

--------------------------------------------------------------------------------
\* SubmitProposalStep(messages, initialDeposit, proposer, metadata) == 
\*     LET msgRequest == [_tag_ |-> "msg-submit-proposal", messages |-> messages, initialDeposit |-> initialDeposit, proposer |-> proposer, metadata |-> metadata] IN
\*     LET msgResponse == SendSubmitProposal(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* ExecLegacyContentStep(content, authority) == 
\*     LET msgRequest == [_tag_ |-> "msg-exec-legacy-content", content |-> content, authority |-> authority] IN
\*     LET msgResponse == SendExecLegacyContent(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* VoteStep(proposalId, voter, option, metadata) == 
\*     LET msgRequest == [_tag_ |-> "msg-vote", proposalId |-> proposalId, voter |-> voter, option |-> option, metadata |-> metadata] IN
\*     LET msgResponse == SendVote(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* VoteWeightedStep(proposalId, voter, options, metadata) == 
\*     LET msgRequest == [_tag_ |-> "msg-vote-weighted", proposalId |-> proposalId, voter |-> voter, options |-> options, metadata |-> metadata] IN
\*     LET msgResponse == SendVoteWeighted(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* DepositStep(proposalId, depositor, amount) == 
\*     LET msgRequest == [_tag_ |-> "msg-deposit", proposalId |-> proposalId, depositor |-> depositor, amount |-> amount] IN
\*     LET msgResponse == SendDeposit(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* UpdateParamsStep(authority, params) == 
\*     LET msgRequest == [_tag_ |-> "msg-update-params", authority |-> authority, params |-> params] IN
\*     LET msgResponse == SendUpdateParams(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

--------------------------------------------------------------------------------
\* NoRequest == 
\*     [_tag_ |-> "no-request"]

\* NoResponse == 
\*     [_tag_ |-> "no-response"]

\* Init == 
\*     /\ request = NoRequest
\*     /\ response = NoResponse

\* Next == 
\*     \/ \E messages \in Seq(SdkMsg), initialDeposit \in Coins, proposer \in Address, metadata \in STRING:
\*         SubmitProposalStep(messages, initialDeposit, proposer, metadata)

\*     \/ \E content \in Content, authority \in STRING:
\*         ExecLegacyContentStep(content, authority)

\*     \/ \E proposalId \in ProposalId, voter \in Address, option \in VoteOption, metadata \in STRING:
\*         VoteStep(proposalId, voter, option, metadata)

\*     \/ \E proposalId \in ProposalId, voter \in Address, options \in Seq(WeightedVoteOption), metadata \in STRING:
\*         VoteWeightedStep(proposalId, voter, options, metadata)

\*     \/ \E proposalId \in ProposalId, depositor \in Address, amount \in Coins:
\*         DepositStep(proposalId, depositor, amount)

\*     \/ \E authority \in Address, params \in Params:
\*         UpdateParamsStep(authority, params)

--------------------------------------------------------------------------------
\* TODO: auto-generate
\* @type: Set($request);
MsgRequests == 
    MsgSubmitProposal \cup 
    \* MsgExecLegacyContent \cup
    MsgVote \cup 
    MsgVoteWeighted \cup 
    MsgDeposit
    \* MsgUpdateParams

\* TODO: auto-generate
\* @type: Set($response);
MsgResponses == 
    MsgSubmitProposalResponse \cup 
    \* MsgExecLegacyContentResponse \cup
    MsgVoteResponse \cup 
    MsgVoteWeightedResponse \cup 
    MsgDepositResponse
    \* MsgUpdateParamsResponse

\* @type: $request;
NoRequest == 
    [_tag_ |-> "no-request"]

\* @type: $response;
NoResponse == 
    [_tag_ |-> "no-response"]

================================================================================
File automatically generated from cosmos/gov/v1/tx.proto on 2022-11-18 14:11:54 CET
