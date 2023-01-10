----- MODULE MsgErrors -----

\* https://github.com/cosmos/cosmos-sdk/blob/95e65fe4cfd5c5277a1d4dfeea9f766fcb432462/x/gov/types/errors.go#L8
DEPOSIT_NON_POSITIVE == "deposit non positive"
UNKNOWN_PROPOSAL == "unknown proposal"
INACTIVE_PROPOSAL == "inactive proposal"
INVALID_VOTE == "invalid vote"
INSUFFICIENT_FUNDS == "insufficient funds"

Errors == {
    DEPOSIT_NON_POSITIVE,
    UNKNOWN_PROPOSAL,
    INACTIVE_PROPOSAL,
    INVALID_VOTE,
    INSUFFICIENT_FUNDS,
    "none"
}

========