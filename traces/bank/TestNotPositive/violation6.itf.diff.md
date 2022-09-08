# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`init`|`send`|
|`action.coins`|`None`|`<<[ amount \|-> 30, denom \|-> "muon" ], [ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Eve"`|
|`action.sender`|`None`|`"Carol"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>, <<"Bob", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>})`|`None`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|``|`INSUFFICIENT_FUNDS`|

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
|`action.receiver`|`Eve`|`Carol`|
|`action.sender`|`Carol`|`Eve`|
|`action.coins[1]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "atom" ]`|`[ amount \|-> 200, denom \|-> "atom" ]`|
|`action.coins[0]`|`[ amount \|-> 30, denom \|-> "muon" ]`|`[ amount \|-> 200, denom \|-> "muon" ]`|

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
|`action.receiver`|`Carol`|`Bob`|
|`action.sender`|`Eve`|`Bob`|
|`action.coins[1]`|`[ amount \|-> 200, denom \|-> "atom" ]`|`[ amount \|-> 0, denom \|-> "atom" ]`|
|`action.coins[0]`|`[ amount \|-> 200, denom \|-> "muon" ]`|`[ amount \|-> 100, denom \|-> "muon" ]`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|`INSUFFICIENT_FUNDS`|`AMOUNT_NOT_POSITIVE`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`2`|`3`|

</details>

</details>

