
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19, q_20, q_21, q_22, q_23, q_24, q_25, q_26, q_27, q_28, q_29, q_30, q_31 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3 extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
	#(c.location).M_0 < 9 &&
	#(c.location).M_1 < 9 &&
	#(c.location).M_2 < 9 &&
	#(c.location).M_3 < 9
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 9 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_1) + 
		(q_1 -> M_2) + 
		(q_2 -> M_1) + 
		(q_3 -> M_1) + 
		(q_4 -> M_2) + 
		(q_5 -> M_1) + 
		(q_6 -> M_2) + 
		(q_7 -> M_1) + 
		(q_8 -> M_1) + 
		(q_9 -> M_1) + 
		(q_10 -> M_2) + 
		(q_11 -> M_2) + 
		(q_12 -> M_0) + 
		(q_13 -> M_1) + 
		(q_14 -> M_2) + 
		(q_15 -> M_2) + 
		(q_16 -> M_2) + 
		(q_17 -> M_0) + 
		(q_18 -> M_3) + 
		(q_19 -> M_0) + 
		(q_20 -> M_3) + 
		(q_21 -> M_3) + 
		(q_22 -> M_0) + 
		(q_23 -> M_0) + 
		(q_24 -> M_0) + 
		(q_25 -> M_0) + 
		(q_26 -> M_0) + 
		(q_27 -> M_3) + 
		(q_28 -> M_3) + 
		(q_29 -> M_3) + 
		(q_30 -> M_3) + 
		(q_31 -> M_3) &&

	let l_431 = l_0.next | l_431.edges = (q_22 -> q_24) &&
	let l_432 = l_431.next | l_432.edges = (q_22 -> q_25) &&
	let l_433 = l_432.next | l_433.edges = (q_22 -> q_26) &&
	let l_434 = l_433.next | l_434.edges = (q_22 -> q_27) &&
	let l_435 = l_434.next | l_435.edges = (q_22 -> q_28) &&
	let l_436 = l_435.next | l_436.edges = (q_22 -> q_29) &&
	let l_437 = l_436.next | l_437.edges = (q_22 -> q_30) &&
	let l_438 = l_437.next | l_438.edges = (q_22 -> q_31) +
                                               (q_23 -> q_24) &&
	let l_439 = l_438.next | l_439.edges = (q_23 -> q_25) &&
	let l_440 = l_439.next | l_440.edges = (q_23 -> q_26) 
}

pred teleport[loc: Qubit -> Machine, r: Qubit -> Qubit, uloc: Qubit -> Machine, tele: Int, utele: Int] {
    all disj q0, q1: Qubit | (q0 -> q1 in r) implies q0.uloc = q1.uloc
    utele = plus[tele, #(uloc - loc)]
}

fact layerTransition {
    all l: circGraph, us: grph/next[l] { 
	teleport[l.location, us.edges, us.location, l.numTele, us.numTele] 
    }
}

pred finalLayer {  
    lte[grph/last.numTele, 1872]
}

run finalLayer for 11 circGraph, 15 Int
