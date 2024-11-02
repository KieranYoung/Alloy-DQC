#!/bin/bash

# qubits, layers, max arity
# python3 random_circ.py 10 50 5 > random_circ/synth.tfc

QUBITS=( 8 32 128 )
ARITYS=( 2 4 16 32 )
LENGTHS=( 100 1000 )
for qubit in ${QUBITS[@]}; do
    for arity in ${ARITYS[@]}; do
        if [ $arity -lt $qubit ]; then
            for layers in ${LENGTHS[@]}; do
                echo "python3 random_circ.py $qubit $layers $arity > random_circ/synth.$qubit.$layers.$arity.tfc"
                python3 random_circ.py $qubit $layers $arity > random_circ/synth.$qubit.$layers.$arity.tfc
            done
        fi
    done
done
