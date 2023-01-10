--------------------------------- MODULE GovMC ---------------------------------
(******************************************************************************)
(******************************************************************************)
EXTENDS GovProperties


\* instance_SdkMsg == {}

instance_Numbers == {-3, -2, -1, 0, 1, 2, 3}

\* instance_DENOM == {"ustake"}

\* instance_DEPOSIT_PERIOD_PARAM == 

instance_MinDeposit == 2

\* See https://github.com/cosmos/cosmos-sdk/blob/142880b04679ec4794d6fe7ac5909807460b06be/x/bank/keeper/keeper.go#L353
instance_GovModuleAccountAddress == "GovModule"

--------------------------------------------------------------------------------
(******************************************************************************)
(* Model instantiation for Apalache. *)
(* https://apalache.informal.systems/docs/apalache/parameters.html?highlight=constinit#constinit-predicate *)
(******************************************************************************)

ConstInit ==
    \* /\ Address = instance_Address
    /\ CoinAmount = instance_Numbers
    \* /\ Real = instance_Numbers
    \* /\ DENOM = instance_DENOM
    /\ MinDeposit = instance_MinDeposit
    /\ GovModuleAccountAddress = instance_GovModuleAccountAddress

--------------------------------------------------------------------------------

\* @type: <<Str, Str>>;
View == 
    <<
        request._tag_, 
        response.error
    >>

================================================================================