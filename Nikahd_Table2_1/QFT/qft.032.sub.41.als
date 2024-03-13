
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
		(q_10 -> M_0) + 
		(q_11 -> M_2) + 
		(q_12 -> M_0) + 
		(q_13 -> M_1) + 
		(q_14 -> M_2) + 
		(q_15 -> M_3) + 
		(q_16 -> M_2) + 
		(q_17 -> M_0) + 
		(q_18 -> M_3) + 
		(q_19 -> M_3) + 
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

	let l_411 = l_0.next | l_411.edges = (q_19 -> q_31) +
                                               (q_20 -> q_21) &&
	let l_412 = l_411.next | l_412.edges = (q_20 -> q_22) &&
	let l_413 = l_412.next | l_413.edges = (q_20 -> q_23) &&
	let l_414 = l_413.next | l_414.edges = (q_20 -> q_24) &&
	let l_415 = l_414.next | l_415.edges = (q_20 -> q_25) &&
	let l_416 = l_415.next | l_416.edges = (q_20 -> q_26) &&
	let l_417 = l_416.next | l_417.edges = (q_20 -> q_27) &&
	let l_418 = l_417.next | l_418.edges = (q_20 -> q_28) &&
	let l_419 = l_418.next | l_419.edges = (q_20 -> q_29) &&
	let l_420 = l_419.next | l_420.edges = (q_20 -> q_30) 
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
