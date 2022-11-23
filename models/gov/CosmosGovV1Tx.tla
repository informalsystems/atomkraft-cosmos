----------------------------- MODULE CosmosGovV1Tx -----------------------------
\* package: cosmos.gov.v1

EXTENDS
    Integers,
    Sequences,
    CosmosBaseV1beta1Coin,
    CosmosGovV1Gov,
    CosmosGovV1Model
    
VARIABLES
    request,
    response
    
Content == 
    STRING

--------------------------------------------------------------------------------
\* MsgSubmitProposal defines an sdk.Msg type that supports submitting arbitrary
\* proposal Content.
MsgSubmitProposal == [ 
    msgType: {"msg-submit-proposal"},

    \* label: repeated
    messages: Seq(SdkMsg),

    \* label: repeated
    initialDeposit: Seq(Coin),

    \* label: optional
    proposer: Address,

    \* metadata is any arbitrary metadata attached to the proposal.
    \* label: optional
    metadata: STRING
]

\* MsgSubmitProposalResponse defines the Msg/SubmitProposal response type.
MsgSubmitProposalResponse == [ 
    msgType: {"msg-submit-proposal-response"},

    error: STRING,

    \* label: optional
    proposalId: ProposalId
]

\* MsgExecLegacyContent is used to wrap the legacy content field into a message.
\* This ensures backwards compatibility with v1beta1.MsgSubmitProposal.
MsgExecLegacyContent == [ 
    msgType: {"msg-exec-legacy-content"},

    \* content is the proposal's content.
    \* label: optional
    content: Content,

    \* authority must be the gov module address.
    \* label: optional
    authority: STRING
]

\* MsgExecLegacyContentResponse defines the Msg/ExecLegacyContent response type.
MsgExecLegacyContentResponse == [ 
    msgType: {"msg-exec-legacy-content-response"},

    error: STRING
]

\* MsgVote defines a message to cast a vote.
MsgVote == [ 
    msgType: {"msg-vote"},

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
MsgVoteResponse == [ 
    msgType: {"msg-vote-response"},

    error: STRING
]

\* MsgVoteWeighted defines a message to cast a vote.
MsgVoteWeighted == [ 
    msgType: {"msg-vote-weighted"},

    \* label: optional
    proposalId: ProposalId,

    \* label: optional
    voter: Address,

    \* label: repeated
    options: Seq(WeightedVoteOption),

    \* label: optional
    metadata: STRING
]

\* MsgVoteWeightedResponse defines the Msg/VoteWeighted response type.
MsgVoteWeightedResponse == [ 
    msgType: {"msg-vote-weighted-response"},

    error: STRING
]

\* MsgDeposit defines a message to submit a deposit to an existing proposal.
MsgDeposit == [ 
    msgType: {"msg-deposit"},

    \* label: optional
    proposalId: ProposalId,

    \* label: optional
    depositor: Address,

    \* label: repeated
    amount: Seq(Coin)
]

\* MsgDepositResponse defines the Msg/Deposit response type.
MsgDepositResponse == [ 
    msgType: {"msg-deposit-response"},

    error: STRING
]

\* MsgUpdateParams is the Msg/UpdateParams request type.
\*
\* Since: cosmos-sdk 0.47
MsgUpdateParams == [ 
    msgType: {"msg-update-params"},

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
MsgUpdateParamsResponse == [ 
    msgType: {"msg-update-params-response"},

    error: STRING
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
\*     LET msgRequest == [msgType |-> "msg-submit-proposal", messages |-> messages, initialDeposit |-> initialDeposit, proposer |-> proposer, metadata |-> metadata] IN
\*     LET msgResponse == SendSubmitProposal(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* ExecLegacyContentStep(content, authority) == 
\*     LET msgRequest == [msgType |-> "msg-exec-legacy-content", content |-> content, authority |-> authority] IN
\*     LET msgResponse == SendExecLegacyContent(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* VoteStep(proposalId, voter, option, metadata) == 
\*     LET msgRequest == [msgType |-> "msg-vote", proposalId |-> proposalId, voter |-> voter, option |-> option, metadata |-> metadata] IN
\*     LET msgResponse == SendVote(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* VoteWeightedStep(proposalId, voter, options, metadata) == 
\*     LET msgRequest == [msgType |-> "msg-vote-weighted", proposalId |-> proposalId, voter |-> voter, options |-> options, metadata |-> metadata] IN
\*     LET msgResponse == SendVoteWeighted(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* DepositStep(proposalId, depositor, amount) == 
\*     LET msgRequest == [msgType |-> "msg-deposit", proposalId |-> proposalId, depositor |-> depositor, amount |-> amount] IN
\*     LET msgResponse == SendDeposit(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* UpdateParamsStep(authority, params) == 
\*     LET msgRequest == [msgType |-> "msg-update-params", authority |-> authority, params |-> params] IN
\*     LET msgResponse == SendUpdateParams(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

--------------------------------------------------------------------------------
\* NoRequest == 
\*     [msgType |-> "no-request"]

\* NoResponse == 
\*     [msgType |-> "no-response"]

\* Init == 
\*     /\ request = NoRequest
\*     /\ response = NoResponse

\* Next == 
\*     \/ \E messages \in Seq(SdkMsg), initialDeposit \in Seq(Coin), proposer \in Address, metadata \in STRING:
\*         SubmitProposalStep(messages, initialDeposit, proposer, metadata)

\*     \/ \E content \in Content, authority \in STRING:
\*         ExecLegacyContentStep(content, authority)

\*     \/ \E proposalId \in ProposalId, voter \in Address, option \in VoteOption, metadata \in STRING:
\*         VoteStep(proposalId, voter, option, metadata)

\*     \/ \E proposalId \in ProposalId, voter \in Address, options \in Seq(WeightedVoteOption), metadata \in STRING:
\*         VoteWeightedStep(proposalId, voter, options, metadata)

\*     \/ \E proposalId \in ProposalId, depositor \in Address, amount \in Seq(Coin):
\*         DepositStep(proposalId, depositor, amount)

\*     \/ \E authority \in Address, params \in Params:
\*         UpdateParamsStep(authority, params)

================================================================================
File automatically generated from cosmos/gov/v1/tx.proto on 2022-11-18 14:11:54 CET
