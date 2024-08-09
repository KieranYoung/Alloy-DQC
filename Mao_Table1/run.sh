#!/bin/bash

MAX_PROC=2
RUN_PROC=0
RAM_PROC=$(( 30 / $MAX_PROC ))

PY="python3 ../tfc2als.py"
FLAGS="-itvof -r $RAM_PROC -e recent --int_bits 8 -l 10"

DIR="./"


cleanup() {
    kill $(jobs -p)
    exit 1
}

trap cleanup SIGINT

files=("clip_206.tfc" "sao2_257.tfc" "ham15_107.tfc" "ham15_298.tfc")
for file in "${files[@]}"; do
#for file in ./*.tfc; do
    echo "$file"

    $PY $FLAGS -a $DIR/$file --qubit_alloc inorder &

    ((RUN_PROC++))
    if ((RUN_PROC >= MAX_PROC))
    then
        wait -n
        ((RUN_PROC--))
    fi
done

wait
