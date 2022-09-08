# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.coins`|`None`|`<<[ amount \|-> 300, denom \|-> "muon" ]>>`|
|`action.receiver`|`None`|`"Eve"`|
|`action.sender`|`None`|`"Alice"`|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 115792089237316195423570985008687907853269984665640564039457584007913129639935>>, <<"muon", 115792089237316195423570985008687907853269984665640564039457584007913129639935>>})>>, <<"Bob", SetAsFun({<<"atom", 115792089237316195423570985008687907853269984665640564039457584007913129639935>>, <<"muon", 115792089237316195423570985008687907853269984665640564039457584007913129639935>>})>>})`|`None`|
|`action.tag`|`init`|`send`|

</details>
<details open>

<summary><code>balances</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`balances("Eve")`|`None`|`SetAsFun({<<"muon", 300>>})`|
|`balances("Alice")("muon")`|`115792089237316195423570985008687907853269984665640564039457584007913129639935`|`115792089237316195423570985008687907853269984665640564039457584007913129639635`|

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
|`action.coins[0].amount`|`300`|`0`|
|`action.coins[0].denom`|`muon`|`atom`|
|`action.receiver`|`Eve`|`Carol`|
|`action.sender`|`Alice`|`Carol`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|`SUCCESS`|`AMOUNT_NOT_POSITIVE`|

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

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`2`|`3`|

</details>

</details>

