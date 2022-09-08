# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins`|`None`|`<<[ amount \|-> 0, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Alice"`|
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
|`action.receiver`|`Alice`|`Dave`|
|`action.sender`|`Bob`|`Dave`|

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
|`action.coins[0].amount`|`0`|`1809251394333065553493296640760748560207343510400633813116524750123642650625`|
|`action.coins[0].denom`|`atom`|`muon`|
|`action.receiver`|`Dave`|`Carol`|
|`action.sender`|`Dave`|`Bob`|

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
|`balances("Dave")`|`None`|`SetAsFun({<<"muon", 2>>})`|
|`balances("Bob")("muon")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`1809251394333065553493296640760748560207343510400633813116524750123642650621`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[0].amount`|`1809251394333065553493296640760748560207343510400633813116524750123642650625`|`2`|
|`action.receiver`|`Carol`|`Dave`|

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
|`step`|`3`|`4`|

</details>

</details>

