# ITF-Diff Markdown

## Step 1 to Step 2

<details open>

<summary>Variables</summary>

<details open>

<summary><code>action</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`action.balances`|`SetAsFun({<<"Alice", SetAsFun({<<"atom", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"gluon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"muon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>})>>, <<"Bob", SetAsFun({<<"atom", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"gluon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>, <<"muon", 57896044618658097711785492504343953926634992332820282019728792003956564819967>>})>>})`|`None`|
|`action.coins`|`None`|`<<[ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639935, denom \|-> "muon" ], [ amount \|-> 0, denom \|-> "muon" ]>>`|
|`action.receiver`|`None`|`"Carol"`|
|`action.sender`|`None`|`"Carol"`|
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
|`action.receiver`|`Carol`|`Alice`|
|`action.sender`|`Carol`|`Alice`|
|`action.coins[1]`|`[ amount \|-> 0, denom \|-> "muon" ]`|`[ amount \|-> 300, denom \|-> "atom" ]`|
|`action.coins[0]`|`[ amount \|-> 115792089237316195423570985008687907853269984665640564039457584007913129639935, denom \|-> "muon" ]`|`[ amount \|-> 57896044618658097711785492504343953926634992332820282019728792003956564819967, denom \|-> "gluon" ]`|

</details>
<details open>

<summary><code>outcome</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`outcome`|`DUPLICATE_DENOM`|`SUCCESS`|

</details>
<details open>

<summary><code>step</code></summary>


|KeyPath|Old|New|
|-|-|-|
|`step`|`1`|`2`|

</details>

</details>

