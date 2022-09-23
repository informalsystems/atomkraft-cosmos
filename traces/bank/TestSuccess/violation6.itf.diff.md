# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"gluon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"muon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>})>>, <<"Bob", SetAsFun({<<"atom", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"gluon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"muon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>})>>})`|`None`|
|`action.coins`|`None`|`<<[ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639934, denom \|-> "muon" ], [ amount \|-> 10, denom \|-> "atom" ], [ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639937, denom \|-> "gluon" ], [ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639937, denom \|-> "atom" ]>>`|
|`action.receiver`|`None`|`"Alice"`|
|`action.sender`|`None`|`"Bob"`|
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
|`action.coins[2]`|`[ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639937, denom \|-> "gluon" ]`|`None`|
|`action.coins[3]`|`[ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639937, denom \|-> "atom" ]`|`None`|
|`action.sender`|`Bob`|`Alice`|
|`action.coins[1]`|`[ amount \|-> 10, denom \|-> "atom" ]`|`[ amount \|-> 3, denom \|-> "atom" ]`|
|`action.coins[0]`|`[ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639934, denom \|-> "muon" ]`|`[ amount \|-> 57896044618658097711785492504343953926634992332820282019728792003956564819968, denom \|-> "gluon" ]`|

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
|`action.receiver`|`Alice`|`Bob`|
|`action.sender`|`Alice`|`Bob`|
|`action.coins[1]`|`[ amount \|-> 3, denom \|-> "atom" ]`|`[ amount \|-> 1, denom \|-> "muon" ]`|
|`action.coins[0]`|`[ amount \|-> 57896044618658097711785492504343953926634992332820282019728792003956564819968, denom \|-> "gluon" ]`|`[ amount \|-> 300, denom \|-> "gluon" ]`|
|`action.coins[2]`|`None`|`[ amount \|-> 100, denom \|-> "atom" ]`|

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

