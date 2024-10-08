#!/bin/bash

PY="python3.12 ./tfc2als.py"
OG_FLAGS="-itvofw -r 13 -e recent --int_bits 8"

MOES=( 8 4 2 0 )
SATS=( "MiniSatJNI" "MiniSatProverJNI" "SAT4J" )

# TODO REMOVE TEST
#DIR="./RLSB-${SATS[0]}"
#$PY $FLAGS -s ${SATS[0]} -a $DIR/2of5d1.tfc -m 2 
#exit 0

DIR="./benchmarks/qce2024"

run() {
    NAME=$1
    AFLAGS=$2
    echo "$PY $FLAGS -s ${SAT} -a $DIR/$NAME.tfc $AFLAGS --outname $DIR/$NAME.$OUTNAME"
    $PY $FLAGS -s ${SAT} -a $DIR/$NAME.tfc $AFLAGS --outname $DIR/$NAME.$OUTNAME
}

for MOE in ${MOES[@]}; do
    FLAGS="$OG_FLAGS --marginoferror $MOE"

    for SAT in ${SATS[@]}; do

        OUTNAME="$SAT-$MOE"

        run 2of5d1        "-m 2"
        run 2-4dec        "-m 3"
        run 6symd2        "-m 2"
        run 9symd2        "-m 3"
        run partity_247   "-m 3"
        run cycle17_3     "-m 3 -b 0 50"
        run rd32_272      "-m 2"
        run ham7_106      "-m 4"
        run rd53_139      "-m 2"
        run rd53_311      "-m 3"
        run add16_174     "-m 3 -l 10"
        run ham15-109-214 "-m 4 -l 20" &
        run qft.016       "-m 3       --qubit_alloc inorder" &
        run qft.032       "-m 4 -l 10 --qubit_alloc inorder" &
        run qft.064       "-m 6 -l  5 --qubit_alloc inorder"
        
        QFT20S=( 2 3 4 5 7 )
        for i in ${QFT20S}; do
            run qft.020   "-m $1 -l 10 --qubit_alloc inorder"
        done

#        run hwb50ps       "-m 5 -l 7" &
#        run hwb100ps      "-m 7 -l 3"
#
#        run qft.128       "-m 8  -l 3 --qubit_alloc inorder"
#        run qft.256       "-m 12 -l 1 --qubit_alloc inorder"

    done

    wait

done
