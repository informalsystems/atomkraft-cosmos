# Reactor for executing x/authz traces

This reactor was tested against Cosmos SDK v0.46.3. From your `cosmos-sdk`
repository, run:

    git switch --detach v0.46.3
    make build install

Then make sure that the path to the compiled `simd` binary is correctly set in
`chain.toml`:

    atomkraft chain config <path-to-binary>
