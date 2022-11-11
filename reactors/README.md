# Reactors

## Authz

Reactor for executing traces generated from the TLA+ model in `models/authz`.

### Set up binary

The authz reactor was tested against Cosmos SDK v0.46.3. 
- From your `cosmos-sdk` repository, run:

        git switch --detach v0.46.3
        make build install

- Then make sure that the path to the compiled `simd` binary is correctly set in
`chain.toml`:

        atomkraft chain config <path-to-binary>

### Execute traces

You can run tests for all generated traces with:

    atomkraft test trace --path traces/authz/ --reactor reactors/authz.py --keypath event.type
