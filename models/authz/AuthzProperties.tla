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
    /\ expectedResponse.error = GRANTER_EQUALS_GRANTEE

NotRequestGrantFailsOnSameAccount == ~ RequestGrantFailsOnSameAccount

\* States in which a grant was requested and the request failed because
\* the grant's authorization expired.
RequestGrantFailsOnExpiredAuth ==
    /\ event.type = "request-grant"
    /\ expectedResponse.ok = FALSE
    /\ expectedResponse.error = AUTH_EXPIRED

NotRequestGrantFailsOnExpiredAuth == ~ RequestGrantFailsOnExpiredAuth

\* States in which a request to revoke a grant succeeds.
RevokeSucceeds ==
    /\ event.type = "request-revoke"
    /\ expectedResponse.ok = TRUE

NotRevokeSucceeds == ~ RevokeSucceeds

RevokeNonExistingGrant ==
    /\ event.type = "request-revoke" 
    /\ expectedResponse.error = AUTH_NOT_FOUND

NotRevokeNonExistingGrant == ~ RevokeNonExistingGrant

\* Execute a send message where that transfer tokens from the grantee, possibly
\* without a granted authorization.
\* @type: Bool;
GranteeExecutes ==
    /\ event.type = "request-execute"
    /\ event.msg.typeUrl = "send"
    /\ event.grantee = event.msg.fromAddress

NotGranteeExecutes == ~ GranteeExecutes

\* @type: Bool;
ExecuteWithoutGrants ==
    /\ event.type = "request-execute"
    /\ grantStore = EmptyStore

NotExecuteWithoutGrants == ~ ExecuteWithoutGrants

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

--------------------------------------------------------------------------------

\* @type: Seq(TRACE) => Bool;
ExpireThenRevoke(trace) ==
    \E i, j \in DOMAIN trace: i < j /\
        LET state1 == trace[i] IN 
        LET state2 == trace[j] IN
        /\ state1.event.type = "expire"
        /\ state2.event.type = "request-revoke" 
        /\ state1.event.grantId = grantIdOfMsgRevoke(state2.event)

NotExpireThenRevoke(trace) == ~ ExpireThenRevoke(trace)

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
            /\ state2.event.grantId = grantIdOfMsgExecute(state3.event)

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
            /\ state2.event.grantId = g1
            /\ state3.event.type = "request-execute" 
            /\ grantIdOfMsgExecute(state3.event) = g1
            /\ LET 
                \* @type: SDK_MSG;
                msg == CHOOSE m \in state3.event.msgs: TRUE IN
                g1.msgTypeUrl = msg.typeUrl

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

\* @type: Seq(TRACE) => Bool;
DelegateThenUndelegate(trace) ==
    \E i, j \in DOMAIN trace: i < j /\
        LET state1 == trace[i] IN 
        LET state2 == trace[j] IN
        /\ state1.event.type = "request-execute"
        /\ state1.event.msgTypeUrl = DELEGATE_TYPE_URL
        /\ state1.expectedResponse.error = "none"
        /\ state2.event.type = "request-execute" 
        /\ state2.event.msgTypeUrl = UNDELEGATE_TYPE_URL
        /\ grantIdOfMsg(state1.event) = grantIdOfMsg(state2.event)

NotDelegateThenUndelegate(trace) == ~ DelegateThenUndelegate(trace)

================================================================================
Created by Hernán Vanzetto on 10 August 2022
Last modified by Hernán Vanzetto on 20 September 2022
