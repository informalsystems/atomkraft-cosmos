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
|`action`|`[ coins \|-> <<[ amount \|-> 1, denom \|-> "muon" ], [ amount \|-> 20, denom \|-> "atom" ]>>, receiver \|-> "Dave", sender \|-> "Bob", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"atom", 20>>, <<"muon", 1>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`1`|


</details>

## Step 3

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 300, denom \|-> "atom" ]>>, receiver \|-> "Eve", sender \|-> "Bob", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"atom", 20>>, <<"muon", 1>>})>>, <<"Eve", SetAsFun({<<"atom", 300>>})>>})`|
|`outcome`|`"SUCCESS"`|
|`step`|`2`|


</details>

## Step 4

<details open>

<summary>Variables</summary>


|KeyPath|Value|
|-|-|
|`action`|`[ coins \|-> <<[ amount \|-> 3, denom \|-> "atom" ], [ amount \|-> 1, denom \|-> "atom" ], [ amount \|-> [  ], denom \|-> "atom" ], [ amount \|-> 2, denom \|-> "atom" ]>>, receiver \|-> "Carol", sender \|-> "Carol", tag \|-> "send" ]`|
|`balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Dave", SetAsFun({<<"atom", 20>>, <<"muon", 1>>})>>, <<"Eve", SetAsFun({<<"atom", 300>>})>>})`|
|`outcome`|`"DUPLICATE_DENOM"`|
|`step`|`3`|


</details>

