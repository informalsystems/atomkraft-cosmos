#!/usr/bin/env bash

INV=${1:-ProposalDepositPeriod}

apalache-mc check --features=no-rows \
    --cinit=ConstInit --length=7 --max-error=5 --view=View --no-deadlock \
    --inv="$INV" \
    GovMC.tla