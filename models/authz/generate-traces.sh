#!/usr/bin/env bash

declare -a tests=("ExpireThenExecute" "ExpireThenRevoke" "GrantFailsThenGrantSucceeds" "ExecuteWithoutGrants")

MAIN_TLA_FILE="AuthzMC.tla"

for TEST in "${tests[@]}"; do
    echo "Sampling $TEST on $MAIN_TLA_FILE..."
    OUT_DIR=./_apalache-out/$TEST
    NEGATED_TEST=Not$TEST
    time apalache-mc check \
        --cinit=ConstInit --length=5 --max-error=20 --view=View \
        --inv=$NEGATED_TEST \
        --out-dir=$OUT_DIR \
        $MAIN_TLA_FILE
    
    LAST_GENERATED_DIR=$(ls -rt $OUT_DIR/$MAIN_TLA_FILE/ | tail -1)
    OUT_DIR=$OUT_DIR/$MAIN_TLA_FILE/$LAST_GENERATED_DIR

    TRACES_DIR=../../traces/authz/$TEST
    mkdir -p $TRACES_DIR
    rm -f $TRACES_DIR/*.itf.json

    echo "cp $OUT_DIR/*.itf.json $TRACES_DIR"
    cp $OUT_DIR/*.itf.json $TRACES_DIR
    rm $TRACES_DIR/violation.itf.json
done
