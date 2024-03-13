
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19 extends Qubit { }

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
	#(c.location).M_0 < 6 &&
	#(c.location).M_1 < 6 &&
	#(c.location).M_2 < 6 &&
	#(c.location).M_3 < 6
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 6 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =

		(q_0 -> M_0) + 
		(q_1 -> M_0) + 
		(q_2 -> M_0) + 
		(q_3 -> M_0) + 
		(q_4 -> M_0) + 
		(q_5 -> M_1) + 
		(q_6 -> M_1) + 
		(q_7 -> M_1) + 
		(q_8 -> M_1) + 
		(q_9 -> M_1) + 
		(q_10 -> M_2) + 
		(q_11 -> M_2) + 
		(q_12 -> M_2) + 
		(q_13 -> M_2) + 
		(q_14 -> M_2) + 
		(q_15 -> M_3) + 
		(q_16 -> M_3) + 
		(q_17 -> M_3) + 
		(q_18 -> M_3) + 
		(q_19 -> M_3)  &&

	let l_1 = l_0.next     | l_1.edges   = (q_0 -> q_1) &&
	let l_2 = l_1.next     | l_2.edges   = (q_0 -> q_2) &&
	let l_3 = l_2.next     | l_3.edges   = (q_0 -> q_3) &&
	let l_4 = l_3.next     | l_4.edges   = (q_0 -> q_4) &&
	let l_5 = l_4.next     | l_5.edges   = (q_0 -> q_5) &&
	let l_6 = l_5.next     | l_6.edges   = (q_0 -> q_6) &&
	let l_7 = l_6.next     | l_7.edges   = (q_0 -> q_7) &&
	let l_8 = l_7.next     | l_8.edges   = (q_0 -> q_8) &&
	let l_9 = l_8.next     | l_9.edges   = (q_0 -> q_9) &&
	let l_10 = l_9.next    | l_10.edges  = (q_0 -> q_10) 
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
