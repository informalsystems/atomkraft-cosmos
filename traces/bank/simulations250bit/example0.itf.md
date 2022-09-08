# ITF Markdown

## Step 1

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ balances \|-> SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>}), tag \|-> "init" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>})`|
|`outcome`|`""`|
|`step`|`0`|


</details>

## Step 2

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "muon" ], [ amount \|-> [  ], denom \|-> "muon" ], [ amount \|-> 2, denom \|-> "atom" ]>>, receiver \|-> "Bob", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>})`|
|`outcome`|`"DUPLICATE_DENOM"`|
|`step`|`1`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "atom" ]>>, receiver \|-> "Eve", sender \|-> "Dave", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>})`|
|`outcome`|`"INSUFFICIENT_FUNDS"`|
|`step`|`2`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "atom" ]>>, receiver \|-> "Dave", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 0>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"atom", [  ]>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`3`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "muon" ]>>, receiver \|-> "Carol", sender \|-> "Bob", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 0>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", 1>>})>>, <<"Carol", SetAsFun({<<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"atom", [  ]>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`4`|


</details>

## Step 6

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "atom" ], [ amount \|-> 1, denom \|-> "muon" ], [ amount \|-> [  ], denom \|-> "atom" ], [ amount \|-> 10, denom \|-> "muon" ]>>, receiver \|-> "Bob", sender \|-> "Dave", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 0>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", 1>>})>>, <<"Carol", SetAsFun({<<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"atom", [  ]>>})>>})`|
|`outcome`|`"DUPLICATE_DENOM"`|
|`step`|`5`|


</details>

