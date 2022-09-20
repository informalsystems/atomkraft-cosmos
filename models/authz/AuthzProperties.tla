--------------------------- MODULE AuthzProperties -----------------------------
EXTENDS Authz, FiniteSets, Integers, Sequences

--------------------------------------------------------------------------------
(******************************************************************************)
(* The following scenarios are described by properties on a single state.     *)
(******************************************************************************)

\* States in which a valid grant was requested (valid meaning that granter is 
\* different than grantee), and the request succeeds. 
RequestGrantSucceeds ==
    /\ event.type = "request-grant"
    /\ event.granter # event.grantee
    /\ expectedResponse.ok = TRUE

NotRequestGrantSucceeds == ~ RequestGrantSucceeds

\* States in which a grant was requested and the request failed because granter
\* and grantee are the same. 
RequestGrantFailsOnSameAccount ==
    /\ event.type = "request-grant"
    /\ expectedResponse.ok = FALSE
    /\ expectedResponse.error = "granter-equal-grantee"

NotRequestGrantFailsOnSameAccount == ~ RequestGrantFailsOnSameAccount

\* States in which a grant was requested and the request failed because
\* the grant's authorization expired.
RequestGrantFailsOnExpiredAuth ==
    /\ event.type = "request-grant"
    /\ expectedResponse.ok = FALSE
    /\ expectedResponse.error = "authorization-expired"

NotRequestGrantFailsOnExpiredAuth == ~ RequestGrantFailsOnExpiredAuth

\* States in which a request to revoke a grant succeeds.
RevokeSucceeds ==
    /\ event.type = "request-revoke"
    /\ expectedResponse.ok = TRUE

NotRevokeSucceeds == ~ RevokeSucceeds

RevokeNonExistingGrant ==
    /\ event.type = "request-revoke" 
    /\ expectedResponse.error = "grant-not-found"

NotRevokeNonExistingGrant == ~ RevokeNonExistingGrant

--------------------------------------------------------------------------------
(******************************************************************************)
(* The following scenarios are described by trace properties on more than one *)
(* state.                                                                     *)
(******************************************************************************)

\* Traces with a state with an expire event and a subsequent state with an
\* execute message on the same grant id.
\* @typeAlias: TRACE = [grantStore: GRANT_ID -> GRANT, event: EVENT, expectedResponse: RESPONSE_MSG];
\* @type: Seq(TRACE) => Bool;
ExpireThenExecute(trace) ==
    \E i, j \in DOMAIN trace: i < j /\
        LET state1 == trace[i] IN 
        LET state2 == trace[j] IN
        /\ state1.event.type = "expire"
        /\ state2.event.type = "request-execute" 
        /\ state1.event.grantId = grantIdOfMsgExecute(state2.event)
        \* /\ Len(trace) = 10

NotExpireThenExecute(trace) == ~ ExpireThenExecute(trace)

\* This property on a single state should be the same as the one above. It
\* implies that before request-execute, there were a request-grant and an expire
\* event.
ExecuteExpired ==
    /\ event.type = "request-execute" 
    /\ expectedResponse.error = "authorization-expired"

NotExecuteExpired == ~ ExecuteExpired

--------------------------------------------------------------------------------

\* @type: Seq(TRACE) => Bool;
ExpireThenRevoke(trace) ==
    \E i, j \in DOMAIN trace: i < j /\
        LET state1 == trace[i] IN 
        LET state2 == trace[j] IN
        /\ state1.event.type = "expire"
        /\ state2.event.type = "request-revoke" 
        /\ state2.event.grantId = grantIdOfMsgRevoke(state1.event)

NotExpireThenRevoke(trace) == ~ ExpireThenRevoke(trace)

--------------------------------------------------------------------------------

\* @typeAlias: TRACE = [grantStore: GRANT_ID -> GRANT, event: EVENT, expectedResponse: RESPONSE_MSG];
\* @type: Seq(TRACE) => Bool;
ExpireThenRevokeFails(trace) ==
    \E i, j \in DOMAIN trace: i < j /\
        LET state1 == trace[i] IN 
        LET state2 == trace[j] IN
        /\ state1.event.type = "expire"
        /\ state2.event.type = "request-revoke" 
        /\ state2.event.grantId = grantIdOfMsgRevoke(state1.event)
        /\ state2.expectedResponse.ok = FALSE

NotExpireThenRevokeFails(trace) == ~ ExpireThenRevokeFails(trace)

--------------------------------------------------------------------------------
\* @type: Seq(TRACE) => Bool;
RequestGrantExpireAndExec(trace) ==
    \E i, j, k \in DOMAIN trace: 
        /\ i < j 
        /\ j < k 
        /\  LET state1 == trace[i] IN 
            LET state2 == trace[j] IN
            LET state3 == trace[k] IN
            /\ state1.event.type = "request-grant"
            /\ state2.event.type = "expire"
            /\ state3.event.type = "request-execute" 
            /\ grantIdOfMsgGrant(state1.event) = state2.event.grantId
            /\ state2.event.grantId = grantIdOfMsgExecute(state1.event)

\* @type: Seq(TRACE) => Bool;
RequestGrantExpireAndExec2(trace) ==
    LET 
        state1 == trace[1] 
        g1 == grantIdOfMsgGrant(state1.event)
    IN
    /\ state1.event.type = "request-grant"
    /\ state1.expectedResponse.ok = TRUE
    /\ \E j, k \in DOMAIN trace: 
        /\ 1 < j 
        /\ j < k 
        /\  LET 
                state2 == trace[j]
                state3 == trace[k] 
            IN
            /\ state2.event.type = "request-expire"
            /\ g1 = grantIdOfMsgRevoke(state2.event)
            /\ state3.event.type = "request-execute" 
            /\ LET 
                \* @type: SDK_MSG;
                msg == CHOOSE m \in state3.event.msgs: TRUE IN
                g1.msgTypeUrl = msg.content.typeUrl

NotRequestGrantExpireAndExec(trace) == ~ RequestGrantExpireAndExec(trace)

\* First a request-grant fails, then a request-grant on the same grant id succeeds.
\* @type: Seq(TRACE) => Bool;
GrantFailsThenGrantSucceeds(trace) ==    
    \E i, j \in DOMAIN trace: i < j /\
        LET state1 == trace[i] IN 
        LET state2 == trace[j] IN
        /\ state1.event.type = "request-grant"
        /\ state1.expectedResponse.ok = FALSE
        /\ state2.event.type = "request-grant"
        /\ state2.expectedResponse.ok = TRUE
        /\ grantIdOfMsgGrant(state1.event) = grantIdOfMsgGrant(state2.event)

NotGrantFailsThenGrantSucceeds(trace) == ~ GrantFailsThenGrantSucceeds(trace)

--------------------------------------------------------------------------------
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

================================================================================
Created by Hernán Vanzetto on 10 August 2022
Last modified by Hernán Vanzetto on 20 September 2022
