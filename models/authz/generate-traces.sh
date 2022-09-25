#!/usr/bin/env bash

declare -a tests=("ExpireThenExecute" "ExpireThenRevoke" "GrantFailsThenGrantSucceeds")

MAIN_TLA_FILE="Authz_MC.tla"

for TEST in "${tests[@]}"; do
    echo "Sampling $TEST on $MAIN_TLA_FILE..."
    OUT_DIR=./_apalache-out/$TEST
    time apalache-mc check \
        --cinit=ConstInit --length=5 --max-error=10 --view=View \
        --inv=Not$TEST \
        --out-dir=$OUT_DIR \
        $MAIN_TLA_FILE
    
    LAST_GENERATED_DIR=$(ls -rt $OUT_DIR/$MAIN_TLA_FILE/ | tail -1)
    OUT_DIR=$OUT_DIR/$MAIN_TLA_FILE/$LAST_GENERATED_DIR

    TRACES_DIR=../../traces/authz/$TEST
    mkdir -p $TRACES_DIR

    echo "cp $OUT_DIR/*.itf.json $TRACES_DIR"
    cp $OUT_DIR/*.itf.json $TRACES_DIR
    rm $TRACES_DIR/violation.itf.json
    # find $OUT_DIR -type f -iname "violation*.itf.json" -not -iname "violation.itf.json" -exec cp {} $TRACES_DIR \;
done
