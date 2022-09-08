------------------------------ MODULE BankSend --------------------------------
EXTENDS Authz, FiniteSets, Integers

(******************************************************************************)

\* Test generation for Cosmos SDK Bank module send functionality 

--------------------------------------------------------------------------------

EXTENDS Apalache, Integers, FiniteSets, Maps, Sequences

VARIABLES
    \* @typeAlias: BALANCES = Str -> (Str -> Int);
    \* @typeAlias: COIN = [denom: Str, amount: Int];
    \* @type: BALANCES;
    balances,
    \* @typeAlias: ACTION = [tag: Str, balances: BALANCES, sender: Str, receiver: Str, coins: Seq(COIN)];
    \* @type: ACTION;
    action,
    \* @type: Str; expected outcome
    outcome,
    \* @type: Int;
    step

MAX == 2^256-1
MAX_SEND_COINS == 3

WALLETS == { "Alice", "Bob", "Carol", "Dave", "Eve" }
DENOMS == { "atom", "muon" }
AMOUNTS == { 0, 1, 2, 3, 10, 20, 30, 100, 200, 300, MAX-2, MAX-1, MAX, MAX+1, MAX+2 }

\* @type: (BALANCES, Str) => (Str -> Int);
GetBalances(b, wallet) ==
  IF wallet \notin DOMAIN b 
  THEN [d \in {} |-> 0 ]
  ELSE b[wallet]

\* @type: (BALANCES, Str, Str) => Int;
GetBalance(b, wallet, denom) ==
  LET bs == GetBalances(b, wallet) IN
  IF denom \notin DOMAIN bs
  THEN 0
  ELSE bs[denom]

\* @type: (ACTION, BALANCES) => Str;
ActionOutcome(a, b) ==
    IF \E c1, c2 \in DOMAIN a.coins: \* no duplicate denoms are allowed
      c1 /= c2 /\ a.coins[c1].denom = a.coins[c2].denom 
      THEN "DUPLICATE_DENOM"
    ELSE IF \E c \in DOMAIN a.coins: \* all coin amounts should be positive
      a.coins[c].amount = 0
      THEN "AMOUNT_NOT_POSITIVE"
    ELSE IF \E c \in DOMAIN a.coins: \* sender should have enough coins
      GetBalance(b, a.sender, a.coins[c].denom) < a.coins[c].amount
      THEN "INSUFFICIENT_FUNDS"
    ELSE IF \E c \in DOMAIN a.coins: \* receiver balance should not overflow
      GetBalance(b, a.receiver, a.coins[c].denom) + a.coins[c].amount > MAX
      THEN "RECEIVER_OVERFLOW"
    ELSE 
      "SUCCESS"

\* @type: (Seq(COIN), Bool) => Seq(COIN);
GuessCoin(coins, bit) ==
  IF bit THEN 
    LET d == Guess(DENOMS) IN 
    LET a == Guess(AMOUNTS) IN 
      Append(coins, [ denom |-> d, amount |-> a ])
  ELSE coins

\* @type: () => Seq(COIN);
GuessCoins == 
  LET GuessBit(i) == Guess(BOOLEAN) IN
  LET bits == MkSeq(4, GuessBit) IN 
  ApaFoldSeqLeft(GuessCoin, <<>>, bits)

\* @type: (ACTION) => Bool;
NewAction(a) ==
  \E sender, receiver \in WALLETS:
    /\ a = [ tag |-> "send", sender |-> sender, receiver |-> receiver, coins |-> GuessCoins ]
    /\ \E i \in DOMAIN a.coins: a.coins[i].denom /= "null"

Init ==
    /\ balances = [ wallet \in {"Alice", "Bob"} |-> [denom \in DENOMS |-> MAX] ]
    /\ action = [ tag |-> "init", balances |-> balances ]
    /\ outcome = ""
    /\ step = 0

\* @type: (Str -> Int, COIN) => Str -> Int;
AddCoin(coins, c) ==
    IF c.denom = "null" THEN coins
    ELSE MapPut(coins, c.denom, c.amount)

\* @type: (ACTION) => Str -> Int;
ActionCoins(a) ==
  ApaFoldSeqLeft(AddCoin, [ x \in {} |-> 0], a.coins)

\* @type: (ACTION) => Bool;
DoAction(a) ==
  \* balances' = balances
  LET coins == ActionCoins(a) IN
  balances' = [
    w \in DOMAIN balances \union {a.sender, a.receiver} |->
      IF w = a.sender THEN 
        LET b == GetBalances(balances, a.sender) IN 
          [d \in DOMAIN b |-> 
            IF d \in DOMAIN coins THEN b[d] - coins[d]
            ELSE b[d]
          ]
      ELSE IF w = a.receiver THEN
        LET b == GetBalances(balances, a.receiver) IN 
          [d \in DOMAIN b \union DOMAIN coins |-> 
            IF d \in DOMAIN b /\ d \in DOMAIN coins THEN b[d] + coins[d]
            ELSE IF d \in DOMAIN coins THEN coins[d]
            ELSE b[d]
            \* Using the below line instead of the above 3 pushes Apalache runtime
            \* for invariant (step < 4) from 90 to 222 seconds
            \* GetBalance(balances, a.receiver, d) + coins[d]
          ]
      ELSE balances[w]
  ]

Next ==
  /\ NewAction(action')
  /\ outcome' = ActionOutcome(action', balances)
  /\ IF outcome' = "SUCCESS" THEN
       DoAction(action')
     ELSE
       UNCHANGED <<balances>>
  /\ step' = step + 1

Ex == step < 3
 
TestOverflow == outcome /= "RECEIVER_OVERFLOW"

Inv == outcome /= "DUPLICATE_DENOM"

View == outcome

================================================================================
Created by Andrey Kuprianov on 8 September 2022
 