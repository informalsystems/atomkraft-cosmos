------------------------------ MODULE MsgErrors --------------------------------
(******************************************************************************)
(* Error messages                                                             *)
(******************************************************************************)

\* x/authz module sentinel errors
\* https://github.com/cosmos/cosmos-sdk/blob/55054282d2df794d9a5fe2599ea25473379ebc3d/x/authz/errors.go#L8
AUTH_NOT_FOUND == "authorization not found" \* code 2
INVALID_EXPIRATION == "expiration time of authorization should be more than current time" \* code 3
UNKNOWN_AUTH == "unknown authorization type" \* code 4
GRANT_KEY_NOT_FOUND == "grant key not found" \* code 5
AUTH_EXPIRED == "authorization expired" \* code 6
GRANTER_EQUALS_GRANTEE == "grantee and granter should be different" \* code 7
MAX_TOKENS_NOT_POSITIVE == "max tokens should be positive" \* code 12

\* Bank
SPEND_LIMIT_MUST_BE_POSITIVE == "spend limit must be positive"
INVALID_COINS == "invalid coins"
INSUFFICIENT_AMOUNT == "requested amount is more than spend limit"
SPEND_LIMIT_IS_NIL == "spend limit cannot be nil"
SPEND_LIMIT_IS_NEGATIVE == "spend limit cannot be negitive"
ADDRESS_NOT_ALLOWED == "cannot send to .* address"

\* Staking
FAILED_TO_EXECUTE == "failed to execute message"
CANNOT_DELEGATE_TO_VALIDATOR == "cannot delegate/undelegate to .* validator"
NEGATIVE_COIN_AMOUNT == "negative coin amount"
INVALID_DELEGATION_AMOUNT == "invalid delegation amount"
INVALID_SHARES_AMOUNT == "invalid shares amount" \* code 18
NO_DELEGATION == "no delegation for (address, validator) tuple" \* code 19; parentheses should be escaped in the reactor; here will break the ITF json files
\* ALLOWED_OR_DENY_IS_EMPTY == "both allowed & deny list cannot be empty"
\* ALLOWED_AND_DENY_SET == "cannot set both allowed & deny list"

================================================================================
Created by Hernán Vanzetto on 14 October 2022
