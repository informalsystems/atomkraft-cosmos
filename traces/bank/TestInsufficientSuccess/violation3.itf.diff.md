# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins`|`None`|`<<[ amount \|-> 0, denom \|-> "muon" ], [ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Carol"`|
|`action.sender`|`None`|`"Bob"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>, <<"Bob", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>})`|`None`|
|`action.tag`|`init`|`send`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|``|`AMOUNT_NOT_POSITIVE`|

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
|`action.coins[1]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "atom" ]`|`None`|
|`action.receiver`|`Carol`|`Dave`|
|`action.sender`|`Bob`|`Alice`|
|`action.coins[0]`|`[ amount \|-> 0, denom \|-> "muon" ]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650625, denom \|-> "atom" ]`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|`AMOUNT_NOT_POSITIVE`|`INSUFFICIENT_FUNDS`|

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
|`balances("Eve")`|`None`|`SetAsFun({<<"atom", 3>>, <<"muon", 1>>})`|
|`balances("Alice")("atom")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`1809251394333065553493296640760748560207343510400633813116524750123642650620`|
|`balances("Alice")("muon")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`1809251394333065553493296640760748560207343510400633813116524750123642650622`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[1]`|`None`|`[ amount \|-> 3, denom \|-> "atom" ]`|
|`action.receiver`|`Dave`|`Eve`|
|`action.coins[0]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650625, denom \|-> "atom" ]`|`[ amount \|-> 1, denom \|-> "muon" ]`|

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

