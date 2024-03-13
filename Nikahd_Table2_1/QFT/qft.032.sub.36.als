
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
		(q_2 -> M_2) + 
		(q_3 -> M_1) + 
		(q_4 -> M_0) + 
		(q_5 -> M_1) + 
		(q_6 -> M_2) + 
		(q_7 -> M_1) + 
		(q_8 -> M_1) + 
		(q_9 -> M_2) + 
		(q_10 -> M_3) + 
		(q_11 -> M_2) + 
		(q_12 -> M_0) + 
		(q_13 -> M_0) + 
		(q_14 -> M_3) + 
		(q_15 -> M_3) + 
		(q_16 -> M_1) + 
		(q_17 -> M_1) + 
		(q_18 -> M_1) + 
		(q_19 -> M_2) + 
		(q_20 -> M_2) + 
		(q_21 -> M_2) + 
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

	let l_361 = l_0.next | l_361.edges = (q_15 -> q_31) +
                                               (q_16 -> q_17) &&
	let l_362 = l_361.next | l_362.edges = (q_16 -> q_18) &&
	let l_363 = l_362.next | l_363.edges = (q_16 -> q_19) &&
	let l_364 = l_363.next | l_364.edges = (q_16 -> q_20) &&
	let l_365 = l_364.next | l_365.edges = (q_16 -> q_21) &&
	let l_366 = l_365.next | l_366.edges = (q_16 -> q_22) &&
	let l_367 = l_366.next | l_367.edges = (q_16 -> q_23) &&
	let l_368 = l_367.next | l_368.edges = (q_16 -> q_24) &&
	let l_369 = l_368.next | l_369.edges = (q_16 -> q_25) &&
	let l_370 = l_369.next | l_370.edges = (q_16 -> q_26) 
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
