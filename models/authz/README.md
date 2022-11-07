# TLA+ model for x/authz

## Requirements

- Apalache v0.25.10

    atomkraft model apalache get 0.25.10

## Generate traces

Run

    ./generate-traces.sh

to generate 25 traces for each of the following properties: `ExpireThenExecute`,
`ExpireThenRevoke`, `GrantFailsThenGrantSucceeds`, `ExecuteWithoutGrants`. The
trace files will be located in `traces/authz`.