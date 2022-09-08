# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.tag`|`init`|`send`|
|`action.coins`|`None`|`<<[ amount \|-> 20, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Dave"`|
|`action.sender`|`None`|`"Bob"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>, <<"Bob", SetAsFun({<<"atom", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>, <<"muon", 1809251394333065553493296640760748560207343510400633813116524750123642650623>>})>>})`|`None`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Bob")("atom")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`1809251394333065553493296640760748560207343510400633813116524750123642650603`|
|`balances("Dave")`|`None`|`SetAsFun({<<"atom", 20>>})`|

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
|`action.coins[0].denom`|`atom`|`muon`|
|`action.sender`|`Bob`|`Alice`|
|`action.coins[0].amount`|`20`|`1809251394333065553493296640760748560207343510400633813116524750123642650621`|

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
|`balances("Dave")("muon")`|`None`|`1809251394333065553493296640760748560207343510400633813116524750123642650621`|
|`balances("Alice")("muon")`|`1809251394333065553493296640760748560207343510400633813116524750123642650623`|`2`|

</details>

</details>

## Step 3 to Step 4

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.receiver`|`Dave`|`Eve`|
|`action.sender`|`Alice`|`Dave`|
|`action.coins[0]`|`[ amount \|-> 1809251394333065553493296640760748560207343510400633813116524750123642650621, denom \|-> "muon" ]`|`[ amount \|-> 10, denom \|-> "atom" ]`|
|`action.coins[1]`|`None`|`[ amount \|-> 2, denom \|-> "muon" ]`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Dave")("atom")`|`20`|`10`|
|`balances("Dave")("muon")`|`1809251394333065553493296640760748560207343510400633813116524750123642650621`|`1809251394333065553493296640760748560207343510400633813116524750123642650619`|
|`balances("Eve")`|`None`|`SetAsFun({<<"atom", 10>>, <<"muon", 2>>})`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`2`|`3`|

</details>

</details>

