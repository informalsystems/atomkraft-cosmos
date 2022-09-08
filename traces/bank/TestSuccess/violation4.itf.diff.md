# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`init`|`send`|
|`action.coins`|`None`|`<<[ amount \|-> 3, denom \|-> "atom" ], [ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "muon" ]>>`|
|`action.receiver`|`None`|`"Bob"`|
|`action.sender`|`None`|`"Alice"`|
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
|`action.coins[1]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "muon" ]`|`None`|
|`action.receiver`|`Bob`|`Carol`|
|`action.sender`|`Alice`|`Bob`|
|`action.coins[0]`|`[ amount \|-> 3, denom \|-> "atom" ]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650623, denom \|-> "muon" ]`|

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
|`step`|`1`|`2`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Carol")`|`None`|`SetAsFun({<<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})`|
|`balances("Bob")("muon")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`0`|

</details>

</details>

