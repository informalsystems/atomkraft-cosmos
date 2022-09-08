# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`init`|`send`|
|`action.coins`|`None`|`<<[ amount \|-> 100, denom \|-> "atom" ], [ amount \|-> 300, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Dave"`|
|`action.sender`|`None`|`"Alice"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>, <<"Bob", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>})`|`None`|

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
|`action.receiver`|`Dave`|`Eve`|
|`action.sender`|`Alice`|`Eve`|
|`action.coins[1]`|`[ amount \|-> 300, denom \|-> "atom" ]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650623, denom \|-> "muon" ]`|
|`action.coins[0]`|`[ amount \|-> 100, denom \|-> "atom" ]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650623, denom \|-> "atom" ]`|

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

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.sender`|`Eve`|`Bob`|
|`action.coins[1].amount`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`3`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Bob")("muon")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`1809251394333065553493296640760748560207343510400633813116524750123642650620`|
|`balances("Eve")`|`None`|`SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 3>>})`|
|`balances("Bob")("atom")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`0`|

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

