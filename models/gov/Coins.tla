--------------------------- MODULE Coins ---------------------------
(******************************************************************************)
(* Coins as a set of Coin. *)
(******************************************************************************)
EXTENDS 
    Base, 
    Integers
    \*, Sequences \*, SequencesExt
    \* FiniteSetsExt

CONSTANTS 
    \* @type: Set(Int);
    CoinAmount

\* @typeAlias: denom = Str;
\* @type: Set($denom);
Denoms == {"ustake"}

\* @typeAlias: coin = [denom: $denom, amount: Int];
\* @type: Set($coin);
Coin == [denom: Denoms, amount: CoinAmount]

\* @type: ($denom, Int) => $coin;
mkCoin(denom, amount) == [denom |-> denom, amount |-> amount]

\* @type: (Int) => $coin;
mkDefaultCoin(amount) == mkCoin("ustake", amount)

--------------------------------------------------------------------------------
\* @typeAlias: coins = $coin;
\* @type: Set($coins);
Coins == Coin

\* @type: ($denom, Int) => $coins;
mkCoins(denom, amount) == [denom |-> denom, amount |-> amount]

\* @type: (Int) => $coins;
mkDefaultCoins(amount) == mkCoins("ustake", amount)

\* @type: $coins;
ZeroCoins == mkDefaultCoins(0)

\* @type: $coins;
NoCoins == mkDefaultCoins(0)

\* TODO: only for coins with one element
\* @type: ($coins, $coins) => $coins;
CoinsMinus(x, y) ==
    IF x.denom = y.denom THEN
        mkCoins(x.denom, x.amount - y.amount)
    ELSE 
        x

\* @type: ($coins, $coins) => $coins;
CoinsPlus(x, y) ==
    IF x.denom = y.denom THEN
        mkCoins(x.denom, x.amount + y.amount)
    ELSE 
        x

\* @type: ($coins, $coins) => Bool;
CoinsLessThan(x, y) ==
    /\ x.denom = y.denom 
    /\ x.amount < y.amount

\* @type: ($coins, $coins) => Bool;
CoinsLessEqual(x, y) ==
    /\ x.denom = y.denom 
    /\ x.amount <= y.amount
    
================================================================================
