--------------------------- MODULE AuthzProperties -----------------------------
EXTENDS Authz, FiniteSets, Integers

(******************************************************************************)

\** Apalache typecheker fails:
\* \* Filter the function `f` by the values in its range. For entries k |-> v, keep
\* \* only the entries where `g(v)` is true.
\* \* @ type: ((a -> b), (b -> Bool)) => (a -> b);
\* FilterRange(f, g(_)) ==
\*     LET dom == {x \in DOMAIN f: g(f[x])} IN
\*     [x \in dom |-> f[x]]

\* \* @type: Int;
\* NumActiveGrants == 
\*     LET activeStore == FilterRange(grantStore, 
\*         LAMBDA grant: grant # NoGrant /\ grant.expirationTime # "past") 
\*     IN
\*     Cardinality(activeStore)

--------------------------------------------------------------------------------

GrantSuccess ==
    /\ lastRequest.type = "grant"
    /\ lastResponse.ok = TRUE

GrantFailedSameAddress ==
    /\ lastRequest.type = "grant"
    /\ lastResponse.ok = FALSE
    /\ lastResponse.error = "granter-equal-grantee"
    
GrantFailedAuthExpired ==
    /\ lastRequest.type = "grant"
    /\ lastResponse.ok = FALSE
    /\ lastResponse.error = "authorization-expired"

RevokeSuccess ==
    /\ lastRequest.type = "revoke"
    /\ lastResponse.ok = TRUE

\* @typeAlias: TRACE = Int -> [lastEvent: EVENT, lastResponse: RESPONSE_MSG];
\* @type: (TRACE) => Bool;
ExpireRevokeFailure(trace) ==
    \E i \in DOMAIN trace:
        LET state1 == trace[i] IN 
        LET state2 == trace[i+1] IN
        /\ state1.lastEvent.type = "expire"
        /\ state2.lastEvent.type = "revoke" 
        /\ state2.lastResponse.ok = FALSE

\* @type: (TRACE) => Bool;
ExpireRevokeFailureSameGrant(trace) ==
    \E i \in DOMAIN trace:
        LET state1 == trace[i] IN 
        LET state2 == trace[i+1] IN
        /\ state1.lastEvent.type = "expire"
        /\ state2.lastEvent.type = "revoke" 
        /\ state2.lastResponse.ok = FALSE
        /\ state1.lastEvent.g = grantIdOfRevoke(state2.lastRequest)

\* \* 3. MIREL Test Case: testing grant failures and then successful creation of grant
\* \* @type: Seq(STATE) => Bool;
\* GrantFailedFollowedBySuccess(trace) ==    
\*     \E i \in DOMAIN trace:
\*         LET state1 == trace[i] IN 
\*         LET state2 == trace[i+1] IN
\*         /\ state1.outcome_status \in GRANT_FAILURE_REASONS
\*         \* /\ state1.outcome_status = GRANT_FAILED
\*         /\ state2.outcome_status = GRANT_SUCCESS            
\*         /\ Len(trace) >= i+1

\* \* 4. MIREL Test Case: testing grant failure, succesful creating grant and then Revoke
\* (* <--- *)
\* \* @type: Seq(STATE) => Bool;
\* GrantFailuresPreconditionsNotMetFollowedBySuccess(trace) ==
\*     \E i \in DOMAIN trace:
\*         LET state1 ==trace[i] IN 
\*         LET state2 == trace [j] IN 
\*         LET state3 == trace [k] IN
\*         LET grant1 == state1.action_taken.grant IN
\*         LET grant2 == state2.action_taken.grant IN
\*         LET grant3 == state3.action_taken.grant IN    
\*         /\ i < j
\*         /\ j < k
\*         /\ state1.outcome_status \in GRANT_FAILURE_REASONS
\*         /\ state2.outcome_status = GRANT_SUCCESS
\*         /\ state3.outcome_status = REVOKE_SUCCESS
\*         /\ grant1 = grant2
\*         /\ grant2 = grant3
\*         /\ Len(trace) >= k

================================================================================