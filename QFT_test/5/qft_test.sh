#!/bin/bash

#python3 ../../tfc2als.py -itvwof -r 10 -e recent --int_bits 8 --qubit_alloc inorder -a ./4_6/qft.5.tfc --uncond --qft_last_loc 2 -l 4 6

FILE=qft.5.tfc

DIR=./4_6
mkdir -p $DIR
rm $DIR/*.out $DIR/*.als $DIR/*.csv $DIR/*.tfc
cp ./$FILE $DIR/$FILE
python3 ../../tfc2als.py -itvwof -r 10 -e recent --int_bits 8 --qubit_alloc inorder -a ./$DIR/$FILE --uncond --qft_last_loc 2 -l 4 6

DIR=./4_3_3
mkdir -p $DIR
rm $DIR/*.out $DIR/*.als $DIR/*.csv $DIR/*.tfc
cp ./$FILE $DIR/$FILE
python3 ../../tfc2als.py -itvwof -r 10 -e recent --int_bits 8 --qubit_alloc inorder -a ./$DIR/$FILE --uncond --qft_last_loc 2 -l 4 3 3

DIR=./4_3_2_1
mkdir -p $DIR
rm $DIR/*.out $DIR/*.als $DIR/*.csv $DIR/*.tfc
cp ./$FILE $DIR/$FILE
python3 ../../tfc2als.py -itvwof -r 10 -e recent --int_bits 8 --qubit_alloc inorder -a ./$DIR/$FILE --uncond --qft_last_loc 2 -l 4 3 2 1
