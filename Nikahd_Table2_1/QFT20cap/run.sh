#!/bin/bash

PY="python3 ../tfc2als.py"
FLAGS="-itvof -r 28 -e recent --int_bits 8"

DIR="./QFT20cap/"


for i in $(seq -s " " 2 1 10); do
    echo "QFT-20 $i"
    cp $DIR/qft.20.tfc $DIR/qft.20.$i.tfc
    $PY $FLAGS -a $DIR/qft.20.$i.tfc -m $i -c 10 --qubit_alloc inorder
done
