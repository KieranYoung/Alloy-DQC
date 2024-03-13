
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
		(q_7 -> M_2) + 
		(q_8 -> M_2) + 
		(q_9 -> M_1) + 
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

	let l_129 = l_0.next | l_129.edges = (q_9 -> q_12) &&
	let l_130 = l_129.next | l_130.edges = (q_9 -> q_13) &&
	let l_131 = l_130.next | l_131.edges = (q_9 -> q_14) &&
	let l_132 = l_131.next | l_132.edges = (q_9 -> q_15) &&
	let l_133 = l_132.next | l_133.edges = (q_9 -> q_16) &&
	let l_134 = l_133.next | l_134.edges = (q_9 -> q_17) &&
	let l_135 = l_134.next | l_135.edges = (q_9 -> q_18) &&
	let l_136 = l_135.next | l_136.edges = (q_9 -> q_19) +
                                               (q_10 -> q_11) &&
	let l_137 = l_136.next | l_137.edges = (q_10 -> q_12) 
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
