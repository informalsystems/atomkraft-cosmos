----------------------------- MODULE GovProperties -----------------------------
(******************************************************************************)
(******************************************************************************)
EXTENDS 
    FiniteSets,
    \* Integers 
    \* Sequences
    Gov

--------------------------------------------------------------------------------
ProposalDepositPeriod ==
    \E proposalId \in DOMAIN proposals: 
        proposals[proposalId].status = "PROPOSAL_STATUS_DEPOSIT_PERIOD"
NotProposalDepositPeriod == ~ ProposalDepositPeriod

ProposalVoting ==
    /\ 1 \in DOMAIN proposals
    /\ proposals[1].status = "PROPOSAL_STATUS_VOTING_PERIOD"
NotProposalVoting == ~ ProposalVoting

ProposalPassed ==
    /\ 1 \in DOMAIN proposals
    /\ proposals[1].status = "PROPOSAL_STATUS_PASSED"
NotProposalPassed == ~ ProposalPassed

ProposalRejected ==
    \E proposalId \in DOMAIN proposals: 
        proposals[proposalId].status = "PROPOSAL_STATUS_REJECTED"
NotProposalRejected == ~ ProposalRejected

--------------------------------------------------------------------------------
TwoProposals == ~ (2 \in DOMAIN proposals)

TwoVotes == ~ (Cardinality(DOMAIN votes) = 2)
FiveVotes == ~ (Cardinality(DOMAIN votes) = 5)

OneDeposit == ~ (
    /\ response._tag_ = "msg-deposit-response"
    /\ response.error = "none"
)

InsufficientFunds == response.error # INSUFFICIENT_FUNDS

================================================================================