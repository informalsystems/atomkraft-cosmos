---------------------------------- MODULE Gov ----------------------------------
(******************************************************************************)
(* Cosmos SDK's gov module. *)
(* version 0.47 *)
(* https://docs.cosmos.network/v0.47/modules/gov *)
(******************************************************************************)
EXTENDS 
    Maps,
    FiniteSets, 
    FiniteSetsExt, \* for SumSet
    CosmosGovV1Tx, 
    MsgErrors
    \* Apalache \* for generating sequences with Gen(_)

\* @typeAlias: voteKey = [proposalId: $proposalId, voter: $address];
\* @type: Set($voteKey);
VoteKeys == [proposalId: ProposalId, voter: Address]

VARIABLES 
    
    \* Proposal objects are used to tally votes and generally track the proposal's
    \* state. They contain an array of arbitrary sdk.Msg's which the governance
    \* module will attempt to resolve and then execute if the proposal passes.
    \* Proposal's are identified by a unique id and contains a series of
    \* timestamps: submit_time, deposit_end_time, voting_start_time,
    \* voting_end_time which track the lifecycle of a proposal.
    \* @type: ($proposalId) -> $proposal;
    proposals,
    
    \* @type: $voteKey -> Set($weightedVoteOption);
    votes,
    
    \* @typeAlias: balances = ($address) -> $coins;
    \* @type: $balances;
    balances \* For deposits.

CONSTANTS
    \* DEPOSIT_PERIOD_PARAM,

    \* @type: Int;
    MinDeposit,

    \* Module Accounts can be used by modules to allocate tokens and in special
    \* cases mint or burn tokens. At a base level these module accounts are capable
    \* of sending/receiving tokens to and from auth.Accounts and other module
    \* accounts.
    \* See https://github.com/cosmos/cosmos-sdk/blob/142880b04679ec4794d6fe7ac5909807460b06be/x/bank/keeper/keeper.go#L353
    \* @type: $address;
    GovModuleAccountAddress 

\* TODO: auto-generate with annotation
EmptyTallyResult == [ 
    _tag_ |-> "tally-result",
    yesCount |-> 0,
    abstainCount |-> 0,
    noCount |-> 0,
    noWithVetoCount |-> 0
]

\* NoWeightedVoteOption == [ 
\*     _tag_ |-> "weighted-vote-option",
\*     option |-> "VOTE_OPTION_UNSPECIFIED",
\*     weight |-> 0
\* ]

\* @type: $vote;
NoVote == [ 
    _tag_ |-> "vote",
    proposalId |-> -1,
    voter |-> "no-address",
    options |-> {},
    metadata |-> ""
]

\* @type: $proposal;
NoProposal == [
    _tag_ |-> "proposal", 
    id |-> 0, 
    \* messages |-> <<>>, 
    message |-> NoMessage, 
    status |-> "PROPOSAL_STATUS_UNSPECIFIED",
    finalTallyResult |-> EmptyTallyResult,
    submitTime |-> NoTimestamp,
    depositEndTime |-> NoTimestamp,
    totalDeposit |-> ZeroCoins,
    votingStartTime |-> NoTimestamp,
    votingEndTime |-> NoTimestamp,
    metadata |-> ""
]

AllAddresses ==  Address \cup {GovModuleAccountAddress}

TypeOK ==
    /\ request \in MsgRequests \cup {NoRequest}
    /\ response \in MsgResponses \cup {NoResponse}
    /\ IsMap(proposals, ProposalId, Proposal)
    /\ IsMap(votes, VoteKeys, SUBSET WeightedVoteOption)
    /\ balances \in [AllAddresses -> Coins]

--------------------------------------------------------------------------------
\* @type: Bool;
Init == 
    \* /\ CosmosGovV1beta1Tx!Init
    /\ request = NoRequest
    /\ response = NoResponse
    /\ proposals = [x \in {} |-> NoProposal]
    /\ votes = [x \in {} |-> {}]
    /\ balances = [a \in AllAddresses |-> mkDefaultCoins(2)]

MaxProposalId ==
    CHOOSE maxId \in (DOMAIN proposals) \cup {0}: 
        \A id \in DOMAIN proposals: maxId >= id

--------------------------------------------------------------------------------
(******************************************************************************)
(* Submit proposal.                                                           *)
(* Right to submit a proposal

Every account can submit proposals by sending a MsgSubmitProposal transaction.
Once a proposal is submitted, it is identified by its unique proposalID.

Proposal Messages

A proposal includes an array of sdk.Msgs which are executed automatically if the
proposal passes. The messages are executed by the governance ModuleAccount
itself. Modules such as x/upgrade, that want to allow certain messages to be
executed by governance only should add a whitelist within the respective msg
server, granting the governance module the right to execute the message once a
quorum has been reached. The governance module uses the MsgServiceRouter to
check that these messages are correctly constructed and have a respective path
to execute on but do not perform a full validity check. *)
(******************************************************************************)
EmptyProposal == [_tag_ |-> "no-proposal", id |-> -1]

\* @type: ($address, $address, $coins) => $balances;
SendCoins(sender, recipient, amount) ==
    [balances EXCEPT ![sender] = CoinsMinus(@, amount), ![recipient] = CoinsPlus(@, amount)]
    \* LET balances1 == 
    \*     \* @ type: $balances;
    \*     MapPut(balances, sender, CoinsMinus(balances[sender], amount)) IN
    \* MapPut(balances1, recipient, CoinsPlus(balances[recipient], amount))

\* update the governance module's account coins pool
\* SendCoinsFromAccountToModule transfers coins from an AccAddress to a ModuleAccount.
\* It will panic if the module account does not exist.
\* https://github.com/cosmos/cosmos-sdk/blob/142880b04679ec4794d6fe7ac5909807460b06be/x/bank/keeper/keeper.go#L350
SendCoinsFromAccountToModule(sender, recipient, amount) == 
    SendCoins(sender, recipient, amount)

\* https://github.com/cosmos/cosmos-sdk/blob/91ca57bcef222b3581a9e6506b7f2b082cccb79c/x/gov/keeper/proposal.go#L15
\* SubmitProposals(message, initialDeposit, metadata) ==
\*     LET 
\*         id == MaxProposalId + 1
\*         status == IF CoinsLessEqual(mkDefaultCoins(MinDeposit), initialDeposit) THEN 
\*                 "PROPOSAL_STATUS_VOTING_PERIOD" 
\*             ELSE 
\*                 "PROPOSAL_STATUS_DEPOSIT_PERIOD"
        
\*         proposal == [
\*             _tag_ |-> "proposal", 
\*             id |-> id, 
\*             \* messages |-> messages, 
\*             message |-> message, 
\*             status |-> status,
\*             finalTallyResult |-> EmptyTallyResult,
            
\*             \* Check values:
\*             submitTime |-> "TS_NOW", \* Timestamp
\*             depositEndTime |-> "TS_NOW_PLUS_DEPOSIT_PERIOD_PARAM",
\*             totalDeposit |-> initialDeposit,
\*             votingStartTime |-> "TS_NONE",
\*             votingEndTime |-> "TS_NONE",
\*             metadata |-> metadata
\*         ]
\*     IN
\*     \* check in code: "Loop through all messages and confirm that each has a handler and the gov module account as the only signer"
\*     \* check in code: InsertInactiveProposalQueue
\*     [proposal |-> proposal, error |-> "none"]

\* https://github.com/cosmos/cosmos-sdk/blob/f001b467a005bb0164563f43f6a04af6403b1fcd/x/gov/keeper/msg_server.go#L30
\* @type: ($sdkMsg, $coins, $address, Str) => Bool;
SubmitProposalStep(message, initialDeposit, proposer, metadata) == 
    LET
        msgRequest == [
            _tag_ |-> "msg-submit-proposal", 
            \* messages |-> <<message>>, 
            message |-> message, 
            initialDeposit |-> initialDeposit, 
            proposer |-> proposer, 
            metadata |-> metadata
        ]
        proposalId == MaxProposalId + 1
        activatedVotingPeriod == CoinsLessEqual(mkDefaultCoin(MinDeposit), initialDeposit)
        status == IF activatedVotingPeriod THEN "PROPOSAL_STATUS_VOTING_PERIOD" ELSE "PROPOSAL_STATUS_DEPOSIT_PERIOD"
        votingStartTime == IF activatedVotingPeriod THEN "TS_NOW" ELSE "TS_NONE"
        proposal == [
            _tag_ |-> "proposal", 
            id |-> proposalId, 
            \* messages |-> messages, 
            message |-> message, 
            status |-> status,
            finalTallyResult |-> EmptyTallyResult,
            
            \* Check values:
            submitTime |-> "TS_NOW", \* Timestamp
            depositEndTime |-> "TS_NOW_PLUS_DEPOSIT_PERIOD_PARAM",
            totalDeposit |-> initialDeposit,
            votingStartTime |-> votingStartTime,
            votingEndTime |-> "TS_NONE",
            metadata |-> metadata
        ]
        error == 
            IF CoinsLessThan(initialDeposit, ZeroCoins) THEN 
                DEPOSIT_NON_POSITIVE 
            ELSE IF CoinsLessThan(balances[proposer], initialDeposit) THEN 
                INSUFFICIENT_FUNDS
            ELSE 
                "none"
    IN
    \* "When a proposal is submitted, it has to be accompanied by a deposit that must be strictly positive, but can be inferior to MinDeposit."
    /\ request' = msgRequest
    /\ response' = [_tag_ |-> "msg-submit-proposal-response", error |-> error, proposalId |-> proposal.id]
    /\ proposals' = MapPutIf(proposals, proposal.id, proposal, error = "none")
    /\ IF error = "none" THEN
            balances' = SendCoinsFromAccountToModule(proposer, GovModuleAccountAddress, initialDeposit)
        ELSE 
            UNCHANGED <<balances>>
    /\ UNCHANGED <<votes>>

--------------------------------------------------------------------------------
(******************************************************************************)
(* Deposit.                                                                   *)
(* To prevent spam, proposals must be submitted with a deposit in the coins
defined by the MinDeposit param.

When a proposal is submitted, it has to be accompanied with a deposit that must
be strictly positive, but can be inferior to MinDeposit. The submitter doesn't
need to pay for the entire deposit on their own. The newly created proposal is
stored in an inactive proposal queue and stays there until its deposit passes
the MinDeposit. Other token holders can increase the proposal's deposit by
sending a Deposit transaction. If a proposal doesn't pass the MinDeposit before
the deposit end time (the time when deposits are no longer accepted), the
proposal will be destroyed: the proposal will be removed from state and the
deposit will be burned (see x/gov EndBlocker). When a proposal deposit passes
the MinDeposit threshold (even during the proposal submission) before the
deposit end time, the proposal will be moved into the active proposal queue and
the voting period will begin.

The deposit is kept in escrow and held by the governance ModuleAccount until the
proposal is finalized (passed or rejected).

Deposit refund and burn

When a proposal is finalized, the coins from the deposit are either refunded or
burned according to the final tally of the proposal:

- If the proposal is approved or rejected but not vetoed, each deposit will be
automatically refunded to its respective depositor (transferred from the
governance ModuleAccount).
- When the proposal is vetoed with greater than 1/3, deposits will be burned
from the governance ModuleAccount and the proposal information along with its
deposit information will be removed from state.
- All refunded or burned deposits are removed from the state. Events are issued
 when burning or refunding a deposit. *)
(******************************************************************************)

\* Activates voting period when appropriate and returns true in that case, else
\* returns false.
\* https://github.com/cosmos/cosmos-sdk/blob/53519ea5b3f4462c83fd5267911244f7b27db572/x/gov/keeper/deposit.go#L109
\* @typeAlias: addDepositResponse = [error: Str, activatedVotingPeriod: Bool, updatedProposal: $proposal];
\* @type: ($proposalId, $address, $coins) => $addDepositResponse;
AddDeposit(proposalId, depositor, amount) ==
    LET 
        proposal == proposals[proposalId]
        \* @type: $coins;
        updatedDeposit == CoinsPlus(proposal.totalDeposit, amount)
        startVoting == CoinsLessEqual(mkDefaultCoins(MinDeposit), updatedDeposit)
        \* @type: $proposalStatus;
        updatedStatus == IF startVoting THEN "PROPOSAL_STATUS_VOTING_PERIOD" ELSE proposal.status
        \* @type: $proposal;
        \* When updating a record with EXCEPT, Apalache fails with an error, probably there is a bug:
        \* updatedProposal == [proposal EXCEPT !.totalDeposit = updatedDeposit, !.status = updatedStatus]
        updatedProposal == [
            _tag_ |-> "proposal", 
            id |-> proposal.id, 
            message |-> proposal.message, 
            status |-> updatedStatus,
            finalTallyResult |-> proposal.finalTallyResult,
            submitTime |-> proposal.submitTime,
            depositEndTime |-> proposal.depositEndTime,
            totalDeposit |-> updatedDeposit,
            votingStartTime |-> proposal.votingStartTime,
            votingEndTime |-> proposal.votingEndTime,
            metadata |-> proposal.metadata
        ]
    IN
    IF proposalId \notin DOMAIN proposals THEN
        [error |-> UNKNOWN_PROPOSAL, activatedVotingPeriod |-> FALSE, updatedProposal |-> NoProposal]
    ELSE IF /\ proposal.status # "PROPOSAL_STATUS_DEPOSIT_PERIOD"
            /\ proposal.status # "PROPOSAL_STATUS_VOTING_PERIOD" THEN
        [error |-> INACTIVE_PROPOSAL, activatedVotingPeriod |-> FALSE, updatedProposal |-> NoProposal]
    ELSE IF CoinsLessThan(amount, ZeroCoins) THEN 
        [error |-> DEPOSIT_NON_POSITIVE, activatedVotingPeriod |-> FALSE, updatedProposal |-> NoProposal]
    ELSE IF CoinsLessThan(balances[depositor], amount) THEN 
        [error |-> INSUFFICIENT_FUNDS, activatedVotingPeriod |-> FALSE, updatedProposal |-> NoProposal]
    ELSE
        [error |-> "none", activatedVotingPeriod |-> startVoting, updatedProposal |-> updatedProposal]

\* https://github.com/cosmos/cosmos-sdk/tree/v0.46.2/blob/7a6b38f0fc8aff670c6e7ff15d331b16bf3f3854/x/gov/keeper/msg_server.go#L170
DepositStep(proposalId, depositor, amount) == 
    LET 
        msgRequest == [_tag_ |-> "msg-deposit", proposalId |-> proposalId, depositor |-> depositor, amount |-> amount]
        \* @type: $addDepositResponse;
        result == AddDeposit(proposalId, depositor, amount)
    IN
    /\ request' = msgRequest
    /\ response' = [_tag_ |-> "msg-deposit-response", error |-> result.error]
    /\ IF result.activatedVotingPeriod THEN
            proposals' = [proposals EXCEPT ![proposalId] = result.updatedProposal]
        ELSE 
            UNCHANGED <<proposals>>
    /\ IF result.error = "none" THEN
            balances' = SendCoinsFromAccountToModule(depositor, GovModuleAccountAddress, amount)
        ELSE 
            UNCHANGED <<balances>>
    /\ UNCHANGED votes

--------------------------------------------------------------------------------
(******************************************************************************)
(* Vote and weighted vote.                                                    *)
(*
Participants
Participants are users that have the right to vote on proposals. On the Cosmos
Hub, participants are bonded Atom holders. Unbonded Atom holders and other users
do not get the right to participate in governance. However, they can submit and
deposit on proposals.

Note that some participants can be forbidden to vote on a proposal under a
certain validator if:
- participant bonded or unbonded Atoms to said validator after proposal entered
voting period.
- participant became validator after proposal entered voting period.

This does not prevent participant to vote with Atoms bonded to other validators.
For example, if a participant bonded some Atoms to validator A before a proposal
entered voting period and other Atoms to validator B after proposal entered
voting period, only the vote under validator B will be forbidden.

Voting period
Once a proposal reaches MinDeposit, it immediately enters Voting period. We
define Voting period as the interval between the moment the vote opens and the
moment the vote closes. Voting period should always be shorter than Unbonding
period to prevent double voting. The initial value of Voting period is 2 weeks.
*)
(******************************************************************************)

\* Create a single option vote with weight 1
\* https://github.com/cosmos/cosmos-sdk/blob/adf6bf57474db18fcac19cbf9441e236b2dbdb1e/x/gov/types/v1/vote.go#L79
\* NewNonSplitVoteOption(option) == <<[
\*     _tag_ |-> weighted-vote-option,
\*     option |-> option,
\*     weight |-> 1
\* ]>>    


\* @type: ($voteOption) => Bool;
ValidVoteOption(option) ==
    option \in {
        "VOTE_OPTION_YES",
        "VOTE_OPTION_ABSTAIN",
        "VOTE_OPTION_NO",
        "VOTE_OPTION_NO_WITH_VETO"
    }

\* https://github.com/cosmos/cosmos-sdk/blob/25e7f9bee2b35f0211b0e323dd062b55bef987b7/x/gov/types/v1/vote.go#L83
\* @type: ($weightedVoteOption) => Bool;
ValidWeightedVoteOption(option) ==
    /\ option.weight > 0
    /\ option.weight <= 100
    /\ ValidVoteOption(option.option)

(* For a weighted vote to be valid, the options field must not contain duplicate
vote options, and the sum of weights of all options must be equal to 1. *)
\* @type: (Set($weightedVoteOption)) => Bool;
ValidVote(options) ==
    /\ \A o \in options: ValidWeightedVoteOption(o)
    /\ SumSet({o.weight: o \in options}) = 100

\* TODO: auto-generate
\* @type: ($proposalId, $address, Set($weightedVoteOption), Str) => $vote;
mkVote(proposalId, voter, options, metadata) == [
    _tag_ |-> "vote", 
    proposalId |-> proposalId, 
    voter |-> voter, 
    options |-> options, 
    metadata |-> metadata
]

\* Add a vote to a proposal.
\* https://github.com/cosmos/cosmos-sdk/blob/91ca57bcef222b3581a9e6506b7f2b082cccb79c/x/gov/keeper/vote.go#L13
\* @typeAlias: addVoteResponse = [error: Str, vote: $vote];
\* @type: ($proposalId, $address, Set($weightedVoteOption)) => $addVoteResponse;
AddVote(proposalId, voter, options) ==
    LET proposal == proposals[proposalId] IN
    IF proposalId \notin DOMAIN proposals THEN
        [error |-> UNKNOWN_PROPOSAL]
    ELSE IF proposal.status # "PROPOSAL_STATUS_VOTING_PERIOD" THEN 
        [error |-> INACTIVE_PROPOSAL]
    ELSE IF ~ ValidVote(options) THEN 
        [error |-> INVALID_VOTE]
    ELSE 
        [error |-> "none"]

\* https://github.com/cosmos/cosmos-sdk/blob/91ca57bcef222b3581a9e6506b7f2b082cccb79c/x/gov/keeper/msg_server.go#L107
\* @type: ($proposalId, $address, $voteOption, Str) => Bool;
VoteStep(proposalId, voter, option, metadata) == 
    LET 
        \* @type: $msgVote;
        msgRequest == [_tag_ |-> "msg-vote", proposalId |-> proposalId, voter |-> voter, option |-> option, metadata |-> metadata]
        \* @type: $weightedVoteOption;
        weightedVoteOption == [_tag_ |-> "weighted-vote-option", option |-> option, weight |-> 100]
        options == {weightedVoteOption}
        \* @type: $addVoteResponse;
        voteResult == AddVote(proposalId, voter, options) 
    IN
    /\ request' = msgRequest
    /\ votes' = MapPutIf(votes, [proposalId |-> proposalId, voter |-> voter], options, voteResult.error = "none")
    /\ response' = [_tag_ |-> "msg-vote-response", error |-> voteResult.error]
    /\ UNCHANGED <<proposals, balances>>

(*
Weighted Votes

ADR-037 introduces the weighted vote feature which allows a staker to split
their votes into several voting options. For example, it could use 70% of its
voting power to vote Yes and 30% of its voting power to vote No.

Often times the entity owning that address might not be a single individual. For
example, a company might have different stakeholders who want to vote
differently, and so it makes sense to allow them to split their voting power.
Currently, it is not possible for them to do "passthrough voting" and giving
their users voting rights over their tokens. However, with this system,
exchanges can poll their users for voting preferences, and then vote on-chain
proportionally to the results of the poll. 

For a weighted vote to be valid, the options field must not contain duplicate
vote options, and the sum of weights of all options must be equal to 1. *)

\* https://github.com/cosmos/cosmos-sdk/blob/91ca57bcef222b3581a9e6506b7f2b082cccb79c/x/gov/keeper/msg_server.go#L129
\* @type: ($proposalId, $address, Set($weightedVoteOption), Str) => Bool;
VoteWeightedStep(proposalId, voter, options, metadata) == 
    LET 
        \* @type: $msgVoteWeighted;
        msgRequest == [_tag_ |-> "msg-vote-weighted", proposalId |-> proposalId, voter |-> voter, options |-> options, metadata |-> metadata]
        \* @type: $addVoteResponse;
        voteResult == AddVote(proposalId, voter, options)
    IN
    /\ request' = msgRequest
    /\ votes' = MapPutIf(votes, [proposalId |-> proposalId, voter |-> voter], options, voteResult.error = "none")
    /\ response' = [_tag_ |-> "msg-vote-weighted-response", error |-> voteResult.error]
    /\ UNCHANGED <<proposals, balances>>

--------------------------------------------------------------------------------
\* ExecLegacyContentStep(content, authority) == 
\*     LET msgRequest == [_tag_ |-> "msg-exec-legacy-content", content |-> content, authority |-> authority] IN
\*     LET msgResponse == SendExecLegacyContent(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

\* UpdateParamsStep(authority, params) == 
\*     LET msgRequest == [_tag_ |-> "msg-update-params", authority |-> authority, params |-> params] IN
\*     LET msgResponse == SendUpdateParams(msgRequest) IN
\*     /\ request' = msgRequest
\*     /\ response' = msgResponse

--------------------------------------------------------------------------------

\* For a weighted vote to be valid, the options field must not contain duplicate 
\* vote options, and the sum of weights of all options must be equal to 1.
\* ValidWeightedVote(options) ==
\*     /\ \A o1, o2 \in options: o1.option # o2.option
\*     /\ SumSet({o.weight: o \in options}) = 100

(*
The governance process is divided in a few steps that are outlined below:

Proposal submission: Proposal is submitted to the blockchain with a deposit.

Vote: Once deposit reaches a certain value (MinDeposit), proposal is confirmed
and vote opens. Bonded Atom holders can then send TxGovVote transactions to vote
on the proposal.

Execution After a period of time, the votes are tallied and depending on the
result, the messages in the proposal will be executed. *)

Next == 
    \/ \E message \in SdkMsg, initialDeposit \in Coins, proposer \in Address:
        SubmitProposalStep(message, initialDeposit, proposer, "")

    \/ \E proposalId \in ProposalId, depositor \in Address, amount \in Coins:
        DepositStep(proposalId, depositor, amount)

    \/ \E proposalId \in ProposalId, voter \in Address, option \in VoteOption:
        VoteStep(proposalId, voter, option, "")

    \/ \E proposalId \in ProposalId, voter \in Address, options \in SUBSET WeightedVoteOption:
        /\ Cardinality(options) <= 3
        /\ VoteWeightedStep(proposalId, voter, options, "")

================================================================================