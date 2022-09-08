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
|`action`|`[ coins \|-> <<[ amount \|-> [  ], denom \|-> "muon" ]>>, receiver \|-> "Eve", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>})`|
|`outcome`|`"INSUFFICIENT_FUNDS"`|
|`step`|`1`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 0, denom \|-> "muon" ]>>, receiver \|-> "Alice", sender \|-> "Carol", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>})`|
|`outcome`|`"AMOUNT_NOT_POSITIVE"`|
|`step`|`2`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 1, denom \|-> "atom" ]>>, receiver \|-> "Carol", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"atom", 1>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`3`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 20, denom \|-> "muon" ], [ amount \|-> 20, denom \|-> "muon" ]>>, receiver \|-> "Carol", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"atom", 1>>})>>})`|
|`outcome`|`"DUPLICATE_DENOM"`|
|`step`|`4`|


</details>

## Step 6

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 0, denom \|-> "atom" ]>>, receiver \|-> "Dave", sender \|-> "Dave", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"atom", 1>>})>>})`|
|`outcome`|`"AMOUNT_NOT_POSITIVE"`|
|`step`|`5`|


</details>

