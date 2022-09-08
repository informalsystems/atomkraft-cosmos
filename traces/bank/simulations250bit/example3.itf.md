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
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "muon" ]>>, receiver \|-> "Carol", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", 0>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"muon", [  ]>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`1`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 30, denom \|-> "muon" ]>>, receiver \|-> "Dave", sender \|-> "Dave", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", 0>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"muon", [  ]>>})>>})`|
|`outcome`|`"INSUFFICIENT_FUNDS"`|
|`step`|`2`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "atom" ]>>, receiver \|-> "Eve", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1>>, <<"muon", 0>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"muon", [  ]>>})>>, <<"Eve", SetAsFun({<<"atom", [  ]>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`3`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 0, denom \|-> "muon" ]>>, receiver \|-> "Dave", sender \|-> "Dave", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1>>, <<"muon", 0>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"muon", [  ]>>})>>, <<"Eve", SetAsFun({<<"atom", [  ]>>})>>})`|
|`outcome`|`"AMOUNT_NOT_POSITIVE"`|
|`step`|`4`|


</details>

## Step 6

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 10, denom \|-> "atom" ]>>, receiver \|-> "Dave", sender \|-> "Bob", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1>>, <<"muon", 0>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"atom", 10>>})>>, <<"Eve", SetAsFun({<<"atom", [  ]>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`5`|


</details>

