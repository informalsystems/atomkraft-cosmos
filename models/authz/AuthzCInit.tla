------------------------------ MODULE AuthzCInit -------------------------------
(******************************************************************************)
(* Model instantiation for Apalache. *)
(* https://apalache.informal.systems/docs/apalache/parameters.html?highlight=constinit#constinit-predicate *)
(******************************************************************************)
EXTENDS AuthzProperties

ConstInit ==
    /\ Address = {"a1", "a2"}
    
    \* For Send and Stake authorizations
    /\ Coins = {0,1}

    \* For Generic authorizations
    /\ GenericMsgTypeUrl = "generic/msg/type"

--------------------------------------------------------------------------------

\* View == <<grantStore>>

================================================================================
