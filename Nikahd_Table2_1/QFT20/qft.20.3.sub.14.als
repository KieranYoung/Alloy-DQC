
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2 extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
	#(c.location).M_0 < 8 &&
	#(c.location).M_1 < 8 &&
	#(c.location).M_2 < 8
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 8 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_0) + 
		(q_1 -> M_0) + 
		(q_2 -> M_0) + 
		(q_3 -> M_0) + 
		(q_4 -> M_2) + 
		(q_5 -> M_0) + 
		(q_6 -> M_0) + 
		(q_7 -> M_1) + 
		(q_8 -> M_2) + 
		(q_9 -> M_2) + 
		(q_10 -> M_1) + 
		(q_11 -> M_1) + 
		(q_12 -> M_1) + 
		(q_13 -> M_1) + 
		(q_14 -> M_1) + 
		(q_15 -> M_1) + 
		(q_16 -> M_2) + 
		(q_17 -> M_2) + 
		(q_18 -> M_2) + 
		(q_19 -> M_2) &&

	let l_138 = l_0.next | l_138.edges = (q_10 -> q_13) &&
	let l_139 = l_138.next | l_139.edges = (q_10 -> q_14) &&
	let l_140 = l_139.next | l_140.edges = (q_10 -> q_15) &&
	let l_141 = l_140.next | l_141.edges = (q_10 -> q_16) &&
	let l_142 = l_141.next | l_142.edges = (q_10 -> q_17) &&
	let l_143 = l_142.next | l_143.edges = (q_10 -> q_18) &&
	let l_144 = l_143.next | l_144.edges = (q_10 -> q_19) +
                                               (q_11 -> q_12) &&
	let l_145 = l_144.next | l_145.edges = (q_11 -> q_13) &&
	let l_146 = l_145.next | l_146.edges = (q_11 -> q_14) 
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

run finalLayer for 10 circGraph, 13 Int
