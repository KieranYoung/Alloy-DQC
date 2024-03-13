
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
		(q_6 -> M_0) + 
		(q_7 -> M_1) + 
		(q_8 -> M_1) + 
		(q_9 -> M_2) + 
		(q_10 -> M_3) + 
		(q_11 -> M_2) + 
		(q_12 -> M_0) + 
		(q_13 -> M_3) + 
		(q_14 -> M_3) + 
		(q_15 -> M_2) + 
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

	let l_351 = l_0.next | l_351.edges = (q_15 -> q_21) &&
	let l_352 = l_351.next | l_352.edges = (q_15 -> q_22) &&
	let l_353 = l_352.next | l_353.edges = (q_15 -> q_23) &&
	let l_354 = l_353.next | l_354.edges = (q_15 -> q_24) &&
	let l_355 = l_354.next | l_355.edges = (q_15 -> q_25) &&
	let l_356 = l_355.next | l_356.edges = (q_15 -> q_26) &&
	let l_357 = l_356.next | l_357.edges = (q_15 -> q_27) &&
	let l_358 = l_357.next | l_358.edges = (q_15 -> q_28) &&
	let l_359 = l_358.next | l_359.edges = (q_15 -> q_29) &&
	let l_360 = l_359.next | l_360.edges = (q_15 -> q_30) 
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
