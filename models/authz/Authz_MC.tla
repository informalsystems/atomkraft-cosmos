------------------------------- MODULE Authz_MC --------------------------------
(******************************************************************************)
(* Model Checker parameters                                                   *)
(******************************************************************************)
EXTENDS AuthzProperties

instance_Accounts == {"a1", "a2", "a3"}

instance_Validators == {"v1", "v2", "v3"}

instance_Coins == {0, 1}

instance_NoMaxCoins == -99

--------------------------------------------------------------------------------
(******************************************************************************)
(* Model instantiation for Apalache. *)
(* https://apalache.informal.systems/docs/apalache/parameters.html?highlight=constinit#constinit-predicate *)
(******************************************************************************)

ConstInit ==
    /\ Accounts = instance_Accounts
    /\ Validators = instance_Validators
    
    \* For Send and Stake authorizations
    /\ Coins = instance_Coins
    /\ NoMaxCoins = instance_NoMaxCoins

--------------------------------------------------------------------------------

grantIdOfEvent(e) ==
    IF e.type = "expire" 
    THEN e.grantId
    ELSE grantIdOfMsg(e)

\* @type: <<Str, GRANT_ID, Str>>;
View == <<
    event.type, 
    grantIdOfEvent(event),
    expectedResponse.error
>>

================================================================================
