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
|`action`|`[ coins \|-> <<[ amount \|-> 1, denom \|-> "muon" ]>>, receiver \|-> "Dave", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"muon", 1>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`1`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 10, denom \|-> "atom" ], [ amount \|-> [  ], denom \|-> "muon" ]>>, receiver \|-> "Carol", sender \|-> "Carol", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"muon", 1>>})>>})`|
|`outcome`|`"INSUFFICIENT_FUNDS"`|
|`step`|`2`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 1, denom \|-> "muon" ]>>, receiver \|-> "Eve", sender \|-> "Eve", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"muon", 1>>})>>})`|
|`outcome`|`"INSUFFICIENT_FUNDS"`|
|`step`|`3`|


</details>

## Step 5

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 3, denom \|-> "atom" ]>>, receiver \|-> "Carol", sender \|-> "Alice", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"atom", 3>>})>>, <<"Dave", SetAsFun({<<"muon", 1>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`4`|


</details>

## Step 6

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 1, denom \|-> "atom" ]>>, receiver \|-> "Eve", sender \|-> "Bob", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Carol", SetAsFun({<<"atom", 3>>})>>, <<"Dave", SetAsFun({<<"muon", 1>>})>>, <<"Eve", SetAsFun({<<"atom", 1>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`5`|


</details>

