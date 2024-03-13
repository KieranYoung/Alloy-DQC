
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3, M_4 extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
	#(c.location).M_0 < 5 &&
	#(c.location).M_1 < 5 &&
	#(c.location).M_2 < 5 &&
	#(c.location).M_3 < 5 &&
	#(c.location).M_4 < 5
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 5 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_2) + 
		(q_1 -> M_0) + 
		(q_2 -> M_0) + 
		(q_3 -> M_0) + 
		(q_4 -> M_0) + 
		(q_5 -> M_1) + 
		(q_6 -> M_1) + 
		(q_7 -> M_1) + 
		(q_8 -> M_1) + 
		(q_9 -> M_3) + 
		(q_10 -> M_2) + 
		(q_11 -> M_2) + 
		(q_12 -> M_3) + 
		(q_13 -> M_3) + 
		(q_14 -> M_3) + 
		(q_15 -> M_4) + 
		(q_16 -> M_4) + 
		(q_17 -> M_4) + 
		(q_18 -> M_4) + 
		(q_19 -> M_2) &&

	let l_21 = l_0.next   | l_21.edges  = (q_1 -> q_4) &&
	let l_22 = l_21.next   | l_22.edges  = (q_1 -> q_5) &&
	let l_23 = l_22.next   | l_23.edges  = (q_1 -> q_6) &&
	let l_24 = l_23.next   | l_24.edges  = (q_1 -> q_7) &&
	let l_25 = l_24.next   | l_25.edges  = (q_1 -> q_8) &&
	let l_26 = l_25.next   | l_26.edges  = (q_1 -> q_9) &&
	let l_27 = l_26.next   | l_27.edges  = (q_1 -> q_10) &&
	let l_28 = l_27.next   | l_28.edges  = (q_1 -> q_11) &&
	let l_29 = l_28.next   | l_29.edges  = (q_1 -> q_12) &&
	let l_30 = l_29.next   | l_30.edges  = (q_1 -> q_13) 
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
    lte[grph/last.numTele, 435]
}

run finalLayer for 11 circGraph, 13 Int
