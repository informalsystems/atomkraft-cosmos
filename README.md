# Atomkraft-cosmos

## Install

| Atomkraft uses Python 3.10. Make sure `python3.10` is installed. |
| ---------------------------------------------------------------- |

Using `brew`

```sh
brew install python
```

Or, if you have `pyenv` installed,

```sh
pyenv install 3.10.6
pyenv global 3.10.6
```

Confirm python version

```sh
python -V # should print `3.10.*`

```

### Install Atomkraft

```sh
python -m pip install -U atomkraft
```

Or, if you want to install the latest changes from atomkraft repository

```
python -m pip install -U git+https://github.com/informalsystems/atomkraft
```

Clone Atomkraft-cosmos repo; requires git

```sh
git clone https://github.com/informalsystems/atomkraft-cosmos
cd atomkraft-cosmos
```

## Testnet set-up

Compile a cosmos-sdk chain binary if you don't have any; requires `make`, `go`, `gcc`

```sh
git submodule update --init --recursive
cd cosmos-sdk
make build
```

If you are using different chain binary, update the chain config accordingly

```sh
atomkraft chain config hrp_prefix cosmos
atomkraft chain config binary ./cosmos-sdk/build/simd
```

## Run tests

```sh
atomkraft test trace --trace traces/special1.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
atomkraft test trace --trace traces/special2.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
```
