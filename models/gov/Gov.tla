---------------------------------- MODULE Gov ----------------------------------
(******************************************************************************)
(* Cosmos SDK's gov module. *)
(******************************************************************************)
EXTENDS Maps, CosmosGovV1Tx

VARIABLES 
    proposals,
    votes,
    balances

CONSTANTS
    DENOM,
    DEPOSIT_PERIOD_PARAM,
    GOV_MODULE_ACCOUNT \* See https://github.com/cosmos/cosmos-sdk/blob/142880b04679ec4794d6fe7ac5909807460b06be/x/bank/keeper/keeper.go#L353

ProposalIds == { p.proposalId: p \in proposals }

Coins == Seq(Coin)
ZeroCoin == [ msgType: {"coin"}, denom: DENOM, amount: "0" ]
ZeroCoins == <<ZeroCoin>>

\* TODO: auto-generate
MsgRequests == 
    MsgSubmitProposal \cup 
    \* MsgExecLegacyContent \cup
    MsgVote \cup 
    MsgVoteWeighted \cup 
    MsgDeposit
    \* MsgUpdateParams

\* TODO: auto-generate
MsgResponses == 
    MsgSubmitProposalResponse \cup 
    \* MsgExecLegacyContentResponse \cup
    MsgVoteResponse \cup 
    MsgVoteWeightedResponse \cup 
    MsgDepositResponse
    \* MsgUpdateParamsResponse

TypeOK ==
    /\ request \in MsgRequests
    /\ response \in MsgResponses
    /\ IsMap(proposals, ProposalIds, Proposal)
    /\ IsMap(votes, ProposalIds \X Address, Vote)
    /\ IsMap(balances, Address, Coins)

MaxProposalId ==
    CHOOSE maxId \in ProposalIds: \A id \in ProposalIds: maxId >= id

\* TODO: auto-generate with annotation
EmptyTallyResult == [ 
    msgType |-> "tally-result",
    yesCount |-> 0,
    abstainCount |-> 0,
    noCount |-> 0,
    noWithVetoCount |-> 0
]

--------------------------------------------------------------------------------
(******************************************************************************)
(* Submit proposal.                                                           *)
(******************************************************************************)
EmptyProposal == [msgType |-> "no-proposal", id |-> -1]

\* https://github.com/cosmos/cosmos-sdk/blob/91ca57bcef222b3581a9e6506b7f2b082cccb79c/x/gov/keeper/proposal.go#L15
SubmitProposals(messages, metadata) ==
    LET id == MaxProposalId + 1 IN
    LET now == "BlockHeader.Time" IN
    LET proposal == [
        msgType |-> "proposal", 
        id |-> id, 
        messages |-> messages, 
        status |-> "PROPOSAL_STATUS_DEPOSIT_PERIOD",
        finalTallyResult |-> EmptyTallyResult,
        submitTime |-> now,
        depositEndTime |-> now + DEPOSIT_PERIOD_PARAM,
        totalDeposit |-> ZeroCoins,
        votingStartTime |-> [msgType |-> "no-time"],
        votingEndTime |-> [msgType |-> "no-time"],
        metadata |-> metadata
    ] IN
    \* check in code: "Loop through all messages and confirm that each has a handler and the gov module account as the only signer"
    \* check in code: InsertInactiveProposalQueue
    [proposal |-> proposal, error |-> "none"]

\* https://github.com/cosmos/cosmos-sdk/blob/f001b467a005bb0164563f43f6a04af6403b1fcd/x/gov/keeper/msg_server.go#L30
SubmitProposalStep(messages, initialDeposit, proposer, metadata) == 
    LET msgRequest == [msgType |-> "msg-submit-proposal", messages |-> messages, initialDeposit |-> initialDeposit, proposer |-> proposer, metadata |-> metadata] IN
    LET result == SubmitProposals(messages, metadata) IN
    LET proposal == result.proposal IN
    /\ request' = msgRequest
    /\ proposals' = MapPutIf(proposals, proposal.id, proposal, result.error = "none")
    /\ response' = [msgType |-> "msg-submit-proposal-response", error |-> result.error, proposalId |-> proposal.id]
    /\ UNCHANGED <<votes, balances>>

--------------------------------------------------------------------------------
(******************************************************************************)
(* Vote and weighted vote.                                                    *)
(******************************************************************************)

\* Create a single option vote with weight 1
\* https://github.com/cosmos/cosmos-sdk/blob/adf6bf57474db18fcac19cbf9441e236b2dbdb1e/x/gov/types/v1/vote.go#L79
\* NewNonSplitVoteOption(option) == <<[
\*     msgType |-> weighted-vote-option,
\*     option |-> option,
\*     weight |-> 1
\* ]>>

ValidVoteOption(option) ==
    option \in {
        "VOTE_OPTION_YES",
        "VOTE_OPTION_ABSTAIN",
        "VOTE_OPTION_NO",
        "VOTE_OPTION_NO_WITH_VETO"
    }

ValidWeightedVoteOption(option) ==
    ValidVoteOption(option.option)

\* TODO: auto-generate
mkVote(proposalId, voter, options, metadata) == [
    msgType |-> "vote", 
    proposalId |-> proposalId, 
    voter |-> voter, 
    options |-> options, 
    metadata |-> metadata
]

\* https://github.com/cosmos/cosmos-sdk/blob/91ca57bcef222b3581a9e6506b7f2b082cccb79c/x/gov/keeper/vote.go#L13
\* @typeAlias: ADD_VOTE_RESPONSE = [error: Str, value: VOTE];
\* @type: (PROPOSAL_ID, ADDRESS, Seq(WEIGHTED_VOTE_OPTION), Str) => ADD_VOTE_RESPONSE;
AddVote(proposalId, voter, options, metadata) ==
    LET proposal == proposals[proposalId] IN
    IF proposalId \notin proposals THEN
        [error |-> "unknown proposal"]
    ELSE IF proposal.status # "PROPOSAL_STATUS_VOTING_PERIOD" THEN 
        [error |-> "inactive proposal"]
    ELSE IF ~ \A opt \in options: ValidWeightedVoteOption(opt) THEN 
        [error |-> "invalid vote"]
    ELSE 
        [error |-> "none", vote |-> mkVote(proposalId, voter, options, metadata)]

\* https://github.com/cosmos/cosmos-sdk/tree/v0.46.2/blob/7a6b38f0fc8aff670c6e7ff15d331b16bf3f3854/x/gov/keeper/msg_server.go#L110
VoteStep(proposalId, voter, option, metadata) == 
    LET msgRequest == [msgType |-> "msg-vote", proposalId |-> proposalId, voter |-> voter, option |-> option, metadata |-> metadata] IN
    LET options == <<[msgType |-> "weighted-vote-option", option |-> option, weight |-> 1]>> IN
    LET voteResult == AddVote(proposalId, voter, options, metadata) IN
    /\ request' = msgRequest
    /\ votes' = MapPutIf(votes, <<proposalId, voter>>, voteResult.vote, voteResult.error = "none")
    /\ response' = [msgType |-> "msg-vote-response", error |-> voteResult.error]
    /\ UNCHANGED <<proposals, balances>>

\* https://github.com/cosmos/cosmos-sdk/tree/v0.46.2/blob/7a6b38f0fc8aff670c6e7ff15d331b16bf3f3854/x/gov/keeper/msg_server.go#L140
VoteWeightedStep(proposalId, voter, options, metadata) == 
    LET msgRequest == [msgType |-> "msg-vote-weighted", proposalId |-> proposalId, voter |-> voter, options |-> options, metadata |-> metadata] IN
    LET voteResult == AddVote(proposalId, voter, options, metadata) IN
    /\ request' = msgRequest
    /\ votes' = MapPutIf(votes, <<proposalId, voter>>, voteResult.vote, voteResult.error = "none")
    /\ response' = [msgType |-> "msg-vote-weighted-response", error |-> voteResult.error]
    /\ UNCHANGED <<proposals, balances>>

--------------------------------------------------------------------------------
(******************************************************************************)
(* Add deposit.                                                               *)
(******************************************************************************)

\* update the governance module's account coins pool
\* SendCoinsFromAccountToModule transfers coins from an AccAddress to a ModuleAccount.
\* It will panic if the module account does not exist.
\* https://github.com/cosmos/cosmos-sdk/blob/142880b04679ec4794d6fe7ac5909807460b06be/x/bank/keeper/keeper.go#L350
SendCoinsFromAccountToModule(sender, recipientModule, amount) ==
    LET recipient == recipientModule.address IN
    LET balances1 == MapPut(balances, sender, balances[sender] - amount) IN
    MapPut(balances1, recipient, balances[recipient] + amount)

\* Activates voting period when appropriate and returns true in that case, else
\* returns false.
\* https://github.com/cosmos/cosmos-sdk/blob/53519ea5b3f4462c83fd5267911244f7b27db572/x/gov/keeper/deposit.go#L109
AddDeposit(proposalId, depositor, amount) ==
    LET proposal == proposals[proposalId] IN
    IF proposalId \notin proposals THEN
        [error |-> "unknown proposal"]
    ELSE IF /\ proposal.status # "PROPOSAL_STATUS_DEPOSIT_PERIOD"
            /\ proposal.status # "PROPOSAL_STATUS_VOTING_PERIOD" THEN
        [error |-> "inactive proposal"]
    ELSE
        [error |-> "none", activatedVotingPeriod |-> TRUE]

\* https://github.com/cosmos/cosmos-sdk/tree/v0.46.2/blob/7a6b38f0fc8aff670c6e7ff15d331b16bf3f3854/x/gov/keeper/msg_server.go#L170
DepositStep(proposalId, depositor, amount) == 
    LET msgRequest == [msgType |-> "msg-deposit", proposalId |-> proposalId, depositor |-> depositor, amount |-> amount] IN
    LET result == AddDeposit(proposalId, depositor, amount) IN
    /\ request' = [msgType |-> "msg-deposit-response", error |-> result.error]
    /\ balances' = MapPutIf(balances, depositor, amount, result.error = "none")
    /\ response' = [msgType |-> "msg-deposit-response", error |-> result.error]
    /\ IF result.activatedVotingPeriod THEN
        SendCoinsFromAccountToModule(depositor, GOV_MODULE_ACCOUNT, amount)
        ELSE UNCHANGED balances
    /\ UNCHANGED <<proposals, votes>>

--------------------------------------------------------------------------------
\* ExecLegacyContentStep(content, authority) == 
\*     LET msgRequest == [msgType |-> "msg-exec-legacy-content", content |-> content, authority |-> authority] IN
\*     LET msgResponse == SendExecLegacyContent(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* UpdateParamsStep(authority, params) == 
\*     LET msgRequest == [msgType |-> "msg-update-params", authority |-> authority, params |-> params] IN
\*     LET msgResponse == SendUpdateParams(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

--------------------------------------------------------------------------------
NoRequest == 
    [msgType |-> "no-request"]

NoResponse == 
    [msgType |-> "no-response"]

NoCoins == [msgType |-> "no-coins"]
NoTimestamp == [msgType |-> "no-time"]
NoVotes == [msgType |-> "no-votes"]

NoProposals == [
    msgType |-> "proposal", 
    id |-> 0, 
    messages |-> <<>>, 
    status |-> "PROPOSAL_STATUS_UNSPECIFIED",
    finalTallyResult |-> EmptyTallyResult,
    submitTime |-> NoTimestamp,
    depositEndTime |-> NoTimestamp,
    totalDeposit |-> NoCoins,
    votingStartTime |-> NoTimestamp,
    votingEndTime |-> NoTimestamp,
    metadata |-> ""
]

Init == 
    \* /\ CosmosGovV1beta1Tx!Init
    /\ request = NoRequest
    /\ response = NoResponse
    /\ proposals = [x \in {} |-> NoProposals]
    /\ votes = [x \in {} |-> NoVotes]
    /\ balances = [x \in {} |-> NoCoins]

Next == 
    \/ \E content \in Content, initialDeposit \in Seq(Coin), proposer \in Address:
        SubmitProposalStep(content, initialDeposit, proposer, "")

    \/ \E proposalId \in ProposalId, voter \in Address, option \in VoteOption:
        VoteStep(proposalId, voter, option, "")

    \/ \E proposalId \in ProposalId, voter \in Address, options \in Seq(WeightedVoteOption):
        VoteWeightedStep(proposalId, voter, options, "")

    \/ \E proposalId \in ProposalId, depositor \in Address, amount \in Seq(Coin):
        DepositStep(proposalId, depositor, amount)

================================================================================