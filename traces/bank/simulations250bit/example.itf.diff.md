# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins`|`None`|`<<[ amount \|-> [  ], denom \|-> "muon" ], [ amount \|-> [  ], denom \|-> "muon" ], [ amount \|-> 2, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Bob"`|
|`action.sender`|`None`|`"Alice"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>, <<"Bob", SetAsFun({<<"atom", [  ]>>, <<"muon", [  ]>>})>>})`|`None`|
|`action.tag`|`init`|`send`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|``|`DUPLICATE_DENOM`|

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

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[2]`|`[ amount \|-> 2, denom \|-> "atom" ]`|`None`|
|`action.receiver`|`Bob`|`Eve`|
|`action.sender`|`Alice`|`Dave`|
|`action.coins[0]`|`[ amount \|-> [  ], denom \|-> "muon" ]`|`[ amount \|-> [  ], denom \|-> "atom" ]`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|`DUPLICATE_DENOM`|`INSUFFICIENT_FUNDS`|

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

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Dave")`|`None`|`SetAsFun({<<"atom", [  ]>>})`|
|`balances("Alice")("atom")`|`[  ]`|`0`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.receiver`|`Eve`|`Dave`|
|`action.sender`|`Dave`|`Alice`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|`INSUFFICIENT_FUNDS`|`SUCCESS`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`2`|`3`|

</details>

</details>

## Step 4 to Step 5

<details open>

<summary>Variables</summary>

<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Carol")`|`None`|`SetAsFun({<<"muon", [  ]>>})`|
|`balances("Bob")("muon")`|`[  ]`|`1`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[0].denom`|`atom`|`muon`|
|`action.receiver`|`Dave`|`Carol`|
|`action.sender`|`Alice`|`Bob`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`3`|`4`|

</details>

</details>

## Step 5 to Step 6

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[1]`|`None`|`[ amount \|-> 1, denom \|-> "muon" ]`|
|`action.coins[3]`|`None`|`[ amount \|-> 10, denom \|-> "muon" ]`|
|`action.receiver`|`Carol`|`Bob`|
|`action.sender`|`Bob`|`Dave`|
|`action.coins[0]`|`[ amount \|-> [  ], denom \|-> "muon" ]`|`[ amount \|-> [  ], denom \|-> "atom" ]`|

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
|`step`|`4`|`5`|

</details>

</details>

