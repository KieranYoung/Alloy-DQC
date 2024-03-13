#!/bin/bash

PY="python3 ../tfc2als.py"
FLAGS="-itvofw -r 13 -e recent --int_bits 8"

DIR="./RLSB"
$PY $FLAGS -a $DIR/2of5d1.tfc -m 2 
$PY $FLAGS -a $DIR/2-4dec.tfc -m 3
$PY $FLAGS -a $DIR/6symd2.tfc -m 2
$PY $FLAGS -a $DIR/9symd2.tfc -m 3
$PY $FLAGS -a $DIR/parity_247.tfc -m 3
$PY $FLAGS -a $DIR/cycle17_3.tfc -m 3 -b 0 50

DIR="./RevLib"
$PY $FLAGS -a $DIR/rd32_272.tfc -m 2
$PY $FLAGS -a $DIR/ham7_106.tfc -m 4
$PY $FLAGS -a $DIR/rd53_139.tfc -m 2
$PY $FLAGS -a $DIR/rd53_311.tfc -m 3
$PY $FLAGS -a $DIR/add16_174.tfc -m 3 -l 10

DIR="./RLSB"
$PY $FLAGS -a $DIR/ham15-109-214.tfc -m 4 -l 20 &

DIR="./QFT"
$PY $FLAGS -a $DIR/qft.016.tfc --qubit_alloc inorder -m 3 &
$PY $FLAGS -a $DIR/qft.032.tfc --qubit_alloc inorder -m 4 -l 10 &
$PY $FLAGS -a $DIR/qft.064.tfc --qubit_alloc inorder -m 6 -l 5

DIR="./QFT20"
for i in {2..10}; do
    $PY $FLAGS -a $DIR/qft.20.$i.tfc --qubit_alloc inorder -l 10 -m $i 
done

DIR="./RLSB"
$PY $FLAGS -a $DIR/hwb50ps.tfc -m 5 -l 7 &
$PY $FLAGS -a $DIR/hwb100ps.tfc -m 7 -l 3

DIR="./QFT"
$PY $FLAGS -a $DIR/qft.128.tfc --qubit_alloc inorder -m 8 -l 3 &
$PY $FLAGS -a $DIR/qft.256.tfc --qubit_alloc inorder -m 12 -l 1
