# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins`|`None`|`<<[ amount \|-> 2, denom \|-> "muon" ], [ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650623, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Carol"`|
|`action.sender`|`None`|`"Alice"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>, <<"Bob", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>})`|`None`|
|`action.tag`|`init`|`send`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Carol")`|`None`|`SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 2>>})`|
|`balances("Alice")("atom")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`0`|
|`balances("Alice")("muon")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`1809251394333065553493296640760748560207343510400633813116524750123642650621`|

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

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[3]`|`None`|`[ amount \|-> 0, denom \|-> "atom" ]`|
|`action.receiver`|`Carol`|`Eve`|
|`action.sender`|`Alice`|`Dave`|
|`action.coins[1]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650623, denom \|-> "atom" ]`|`[ amount \|-> 3, denom \|-> "muon" ]`|
|`action.coins[0]`|`[ amount \|-> 2, denom \|-> "muon" ]`|`[ amount \|-> 1, denom \|-> "atom" ]`|

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
|`action.coins[1]`|`[ amount \|-> 3, denom \|-> "muon" ]`|`None`|
|`action.coins[3]`|`[ amount \|-> 0, denom \|-> "atom" ]`|`None`|
|`action.receiver`|`Eve`|`Carol`|
|`action.sender`|`Dave`|`Carol`|
|`action.coins[0]`|`[ amount \|-> 1, denom \|-> "atom" ]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "atom" ]`|

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
|`balances("Eve")`|`None`|`SetAsFun({<<"atom", 1>>, <<"muon", 2>>})`|
|`balances("Carol")("atom")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`1809251394333065553493296640760748560207343510400633813116524750123642650622`|
|`balances("Carol")("muon")`|`2`|`0`|

</details>
<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins[1]`|`None`|`[ amount \|-> 2, denom \|-> "muon" ]`|
|`action.receiver`|`Carol`|`Eve`|
|`action.coins[0]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650624, denom \|-> "atom" ]`|`[ amount \|-> 1, denom \|-> "atom" ]`|

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

