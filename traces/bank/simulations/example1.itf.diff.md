# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins`|`None`|`<<[ amount \|-> 1, denom \|-> "muon" ], [ amount \|-> 20, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Dave"`|
|`action.sender`|`None`|`"Bob"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>})`|`None`|
|`action.tag`|`init`|`send`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Dave")`|`None`|`SetAsFun({<<"atom", 20>>, <<"muon", 1>>})`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|``|`SUCCESS`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`0`|`1`|

</details>

</details>

## Step 2 to Step 3

<details open>

<summary>Variables</summary>

<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Eve")`|`None`|`SetAsFun({<<"atom", 300>>})`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.receiver`|`Dave`|`Eve`|
|`action.coins[0]`|`[ amount \|-> 1, denom \|-> "muon" ]`|`[ amount \|-> 300, denom \|-> "atom" ]`|
|`action.coins[1]`|`[ amount \|-> 20, denom \|-> "atom" ]`|`None`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`1`|`2`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[1]`|`None`|`[ amount \|-> 1, denom \|-> "atom" ]`|
|`action.coins[2]`|`None`|`[ amount \|-> [  ], denom \|-> "atom" ]`|
|`action.coins[3]`|`None`|`[ amount \|-> 2, denom \|-> "atom" ]`|
|`action.receiver`|`Eve`|`Carol`|
|`action.sender`|`Bob`|`Carol`|
|`action.coins[0]`|`[ amount \|-> 300, denom \|-> "atom" ]`|`[ amount \|-> 3, denom \|-> "atom" ]`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|`SUCCESS`|`DUPLICATE_DENOM`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`2`|`3`|

</details>

</details>

