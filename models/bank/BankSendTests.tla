---------------------------- MODULE BankSendTests ------------------------------
EXTENDS BankSend
(******************************************************************************)
\* Tests for Cosmos SDK Bank module coins send functionality between accounts
--------------------------------------------------------------------------------
\* TLA+ test operators below describe the shape of a test trace you want to see
(******************************************************************************)

\* To generate a trace from e.g. operator ThreeSteps run
\*   atomkraft model sample --model-path models/bank/BankSendTests.tla --examples ThreeSteps --traces-dir traces/bank

\* To generate multiple traces from a single assertion you can add e.g. the following parameters:
\*   --max_error=10 --view=OutcomeView
\* This should generate 10 traces, and the traces should differ according to the OutcomeView operator below,
\* which says that expected outcomes should be different. 
\* You can use other views for focusing on other interesting behaviors.

OutcomeView == outcome
ActionView == outcome
StepView == step

(******************************************************************************)
\* The simplest test assertion: a trace with 3 steps
TestThreeSteps == step = 3

\* The following command generates 10 arbitrary test traces in ./traces/bank/TestThreeSteps directory
\* each trace cosisting of 3 steps, and the traces should differ with each other in expected outcomes:
\*
\*   atomkraft model sample --model-path models/bank/BankSendTests.tla --examples TestThreeSteps --traces-dir traces/bank --max_error=10 --view=OutcomeView

(******************************************************************************)
\* The assertions below require to have a trace with a particular outcome

TestSuccess      == outcome = "SUCCESS"
TestDuplicate    == outcome = "DUPLICATE_DENOM"
TestNotPositive  == outcome = "AMOUNT_NOT_POSITIVE"
TestInsufficient == outcome = "INSUFFICIENT_FUNDS"
TestOverflow     == outcome = "RECEIVER_OVERFLOW"

\* Let's say that now we want to focus on the actions: ActionView requires that actions taken are different. 
\*
\*   atomkraft model sample --model-path models/bank/BankSendTests.tla --examples TestSuccess --traces-dir traces/bank --max_error=10 --view=ActionView


(******************************************************************************)
\* How about writing a test for two consecutive execution steps?
\* In TLA+ this can be done easily: you refer to the next step using primes (') notation;
\* e.g. balances' refers to the wallet balances in the next execution step.

\* In the BankSend model there are these state variables:
\* - balances: a map from wallet names to their balances; each balance is a map from denomination to amount
\* - action: action taken; for "send" action it contains sender, receiver, and coins that are being sent
\* - outcome: the expected outcome of the action taken (see above)
\* - step: the number of the current execution step

\* Two consecutive steps are connected as follows:
\* balances are transformed to balances', by executing action', and the expected outcome is outcome'

\* There is a wallet from which all funds are drained in one step
TestDrainAllFunds ==
  \E wallet \in DOMAIN balances:
    /\ \E denom \in DOMAIN balances[wallet]: balances[wallet][denom] > 0
    /\ \A denom \in DOMAIN balances'[wallet]: balances'[wallet][denom] = 0

\* For some wallet and a denom a send first failed with insufficient funds, but then succeeded
TestInsufficientSuccess ==
  \E wallet \in DOMAIN balances:
  \E denom \in DENOMS:
    /\ action.sender = wallet
    /\ \E c \in DOMAIN action.coins : action.coins[c].denom = denom
    /\ outcome = "INSUFFICIENT_FUNDS"
    /\ action'.sender = wallet
    /\ \E c \in DOMAIN action'.coins : action'.coins[c].denom = denom
    /\ outcome' = "SUCCESS"


(******************************************************************************)
\* Finally, you can describe the shape of a multi-step execution trace as a whole.
\* This is the feature specific to our model checker Apalache; please see
\* https://apalache.informal.systems/docs/apalache/principles/invariants.html#trace-invariants
\* With this approach, a test assertion as an operator over a sequence of states.

\* How about requiring a trace with at least 4 different outcomes?
\* @type: Seq(STATE) => Bool;
TestFourOutcomes(trace) ==
  LET outcomes == { trace[s].outcome : s \in DOMAIN trace \ {1} } IN 
  Cardinality(outcomes) >= 4




================================================================================
Created by Andrey Kuprianov on 8 September 2022


TODO: The test assertion TestFourOutcomes fails; see the issue: https://github.com/informalsystems/atomkraft/issues/145