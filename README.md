# atomkraft-cosmos

## Authz

### Usage

Atomkraft uses Python 3.10. Make sure `python3.10` is installed.

#### Python3.10

```
# install pyenv
pyenv install 3.10.5
pyenv global 3.10.5
```

```
# clone repo; requires `git`
git clone https://github.com/informalsystems/atomkraft-cosmos
cd atomkraft-cosmos

# compile a cosmos-sdk chain binary if you don't have any; requires `make`, `go`, `gcc`
git submodule update --init --recursive
(cd cosmos-sdk; make build)

# if you are using different chain binary, update the chain config accordingly
atomkraft chain config prefix cosmos
atomkraft chain config binary ./cosmos-sdk/build/simd

# prefix for few popular chain binaries
# cosmos-sdk (simd) : cosmos
# cosmoshub (gaiad) : cosmos
# cosmwasm (wasmd) : wasm
# osmosis (osmosisd) : osmo
# juno (junod) : juno

# install python dependencies; requires `poetry`
poetry update

# run tests
poetry run atomkraft test trace --trace traces/special1.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
poetry run atomkraft test trace --trace traces/special2.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
```

### My commands

```
# create atomkraft project
atomkraft init atomkraft-cosmos
cd atomkraft-cosmos

# generate reactor stub
atomkraft reactor --actions "init,give grant,expire grant,revoke grant,execute grant" --variables "Identifiers,Validators,outcome_status,num_execs,action_taken,active_grants,num_grants,expired_grants"

# refactor reactor stub
# ... work ...

# put traces in /trace
cp Authz-Audit/Authz-Atomkraft/examples/cosmos-sdk/traces/AuthzModuleEXT/TracesForTesting/8.GrantSpentFollowedByRevokeFailureCEX/counterexample.itf.json traces/special1.itf.json
cp Authz-Audit/Authz-Atomkraft/examples/cosmos-sdk/traces/AuthzModuleEXT/TracesForTesting/7.ExpiredGrantGivenAgainExecCEX/counterexample.itf.json traces/special2.itf.json

# set action_taken.action_type to "init" for the first states

# add cosmos-sdk repo as git-submodule and compile
git submodule add https://github.com/cosmos/cosmos-sdk
(cd cosmos-sdk; git checkout v0.45.7)
(cd cosmos-sdk; make build)

# configure chain
atomkraft chain config binary ./cosmos-sdk/build/simd

# run test
poetry run atomkraft test trace --trace traces/special1.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
poetry run atomkraft test trace --trace traces/special2.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
```
