# Atomkraft-cosmos

## Install

### Atomkraft-cosmos project
```sh
# Atomkraft uses Python 3.10. Make sure `python3.10` and pyenv are installed.
pyenv install 3.10.5
pyenv global 3.10.5

# install python dependencies; requires `poetry`
poetry update

# Clone Atomkraft-cosmos repo; requires git
git clone https://github.com/informalsystems/atomkraft-cosmos
cd atomkraft-cosmos
```

### Testnet set-up
```sh
# Compile a cosmos-sdk chain binary if you don't have any; requires `make`, `go`, `gcc`
git submodule update --init --recursive
cd cosmos-sdk
make build

# If you are using different chain binary, update the chain config accordingly
atomkraft chain config prefix cosmos
atomkraft chain config binary ./cosmos-sdk/build/simd
```


## Run tests

```sh
# run tests
poetry run atomkraft test trace --trace traces/special1.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
poetry run atomkraft test trace --trace traces/special2.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
```

