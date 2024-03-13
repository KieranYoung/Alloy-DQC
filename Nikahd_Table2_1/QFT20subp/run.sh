#!/bin/bash

PY="python3 ../tfc2als.py"
FLAGS="-itvof -r 28 -e recent --int_bits 8"

DIR="./QFT20subp/"

$PY -a $DIR/qft.20.tfc -m 4 --qubit_alloc inorder

for i in $(seq -s " " 5 5 90); do
    echo "QFT-20 $i"
    cp $DIR/qft.20.als $DIR/qft.20.$i.als
    $PY $FLAGS $DIR/qft.20.$i.als -l $i
done

i=0
cp $DIR/qft.20.als $DIR/qft.20.$i.als
$PY $FLAGS $DIR/qft.20.$i.als
