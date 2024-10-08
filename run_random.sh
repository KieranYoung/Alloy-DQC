#!/bin/bash

PY="python3.12 ./tfc2als.py"
OG_FLAGS="-itvow -r 20 -e recent --int_bits 8"

MOES=( 8 4 2 0 )
SATS=( "MiniSatJNI" "MiniSatProverJNI" "SAT4J" )

# TODO REMOVE TEST
#DIR="./RLSB-${SATS[0]}"
#$PY $FLAGS -s ${SATS[0]} -a $DIR/2of5d1.tfc -m 2 
#exit 0

DIR="./benchmarks/random_circ"

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

        for file in $DIR/*.tfc; do
            name=$(basename $file .tfc)
            echo "$name"
            run $name "-l 10"
        done
    done
done
