
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
		(q_18 -> M_0) + 
		(q_19 -> M_0) + 
		(q_20 -> M_0) + 
		(q_21 -> M_3) + 
		(q_22 -> M_3) + 
		(q_23 -> M_3) + 
		(q_24 -> M_3) + 
		(q_25 -> M_0) + 
		(q_26 -> M_0) + 
		(q_27 -> M_3) + 
		(q_28 -> M_3) + 
		(q_29 -> M_3) + 
		(q_30 -> M_0) + 
		(q_31 -> M_3) &&

	let l_450 = l_0.next | l_450.edges = (q_24 -> q_30) &&
	let l_451 = l_450.next | l_451.edges = (q_24 -> q_31) +
                                               (q_25 -> q_26) &&
	let l_452 = l_451.next | l_452.edges = (q_25 -> q_27) &&
	let l_453 = l_452.next | l_453.edges = (q_25 -> q_28) &&
	let l_454 = l_453.next | l_454.edges = (q_25 -> q_29) &&
	let l_455 = l_454.next | l_455.edges = (q_25 -> q_30) &&
	let l_456 = l_455.next | l_456.edges = (q_25 -> q_31) +
                                               (q_26 -> q_27) &&
	let l_457 = l_456.next | l_457.edges = (q_26 -> q_28) &&
	let l_458 = l_457.next | l_458.edges = (q_26 -> q_29) 
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

run finalLayer for 10 circGraph, 15 Int
