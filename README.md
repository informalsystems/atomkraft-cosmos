Atomkraft-powered Test Suite for Cosmos blockchains
===

[Atomkraft](https://github.com/informalsystems/atomkraft) is a tool for E2E testing of Cosmos SDK blockchains. The distinctive characteristic of Atomkraft tests is that they are _model-based_: a TLA+ model is currently needed to automatically generate the test scenarios. But as soon as the model is in place, massive test suites can be generated and executed against the real blockchain at a press of a button, thanks to the power provided to you by Atomkraft and our in-house model checker [Apalache](https://apalache.informal.systems).

**In this repository, we have started a collective effort of providing the Cosmos community with Atomkraft-powered standard test suite for Cosmos SDK modules.** Our final goal is to provide any Cosmos SDK compatible blockchain with the ability to integrate this test suite into their CI, thus ensuring that the core functionality of Cosmos SDK works as expected in the context of the respective blockchain.

| ⚠️ The repository is very much work-in-progress; we are constantly refining and restructuring it. **The test suite is not yet production ready.** Please feel free to experiment, but problems and errors are to be expected. ⚠️ |

## Installation

1. Please install Atomkraft by following it's [Installation Guide](https://github.com/informalsystems/atomkraft/blob/dev/INSTALLATION.md) to correctly install all dependencies.

2. Clone Atomkraft-cosmos repo.
    ```sh
    git clone https://github.com/informalsystems/atomkraft-cosmos
    cd atomkraft-cosmos
    ```

3. The repo comes preconfigured to use Cosmos SDK binary (`simd`); Cosmos SDK repository is included as Git submodule in this repo. If this is your intention, then just do
    ```sh
    git submodule update --init --recursive
    (cd cosmos-sdk; make build)
    ```

4. (Skip this step if using vanilla Cosmos SDK) If you want to test a custom Cosmos SDK compatible blockchain binary, then you need to have it on your locally on your machine. Please update the [Atomkraft chain config](chain.toml) either manually, or by using these commands:
    ```sh
    atomkraft chain config prefix <YOUR-PREFIX>
    atomkraft chain config binary <PATH-TO-YOUR-BINARY>
    ```

5. Make sure you can run your blockchain binary using Atomkraft by issuing this command `atomkraft chain testnet`. If it works, you are ready to go!

## Running the tests

```sh
# run tests
poetry run atomkraft test trace --trace traces/special1.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
poetry run atomkraft test trace --trace traces/special2.itf.json --reactor reactors/reactor.py --keypath action_taken.action_type
```

