------------------------------- MODULE Authz_MC --------------------------------
(******************************************************************************)

(******************************************************************************)
EXTENDS AuthzProperties

instance_Address == {"a1", "a2"}

instance_Coins == {0, 1}

\* For Generic authorization
instance_GenericAuthTypes == { "msg_alpha" }

--------------------------------------------------------------------------------
(******************************************************************************)
(* Model instantiation for Apalache. *)
(* https://apalache.informal.systems/docs/apalache/parameters.html?highlight=constinit#constinit-predicate *)
(******************************************************************************)

ConstInit ==
    /\ Address = instance_Address
    
    \* For Send and Stake authorizations
    /\ Coins = instance_Coins

    \* For Generic authorization
    /\ GenericAuthTypes = instance_GenericAuthTypes

--------------------------------------------------------------------------------
NumRequests == numRequests # 10

--------------------------------------------------------------------------------

\* View == <<grantStore>>

================================================================================
