
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
		(q_0 -> M_1) + 
		(q_1 -> M_1) + 
		(q_2 -> M_1) + 
		(q_3 -> M_2) + 
		(q_4 -> M_4) + 
		(q_5 -> M_0) + 
		(q_6 -> M_3) + 
		(q_7 -> M_2) + 
		(q_8 -> M_2) + 
		(q_9 -> M_2) + 
		(q_10 -> M_3) + 
		(q_11 -> M_1) + 
		(q_12 -> M_3) + 
		(q_13 -> M_3) + 
		(q_14 -> M_4) + 
		(q_15 -> M_4) + 
		(q_16 -> M_4) + 
		(q_17 -> M_0) + 
		(q_18 -> M_0) + 
		(q_19 -> M_0) &&

	let l_101 = l_0.next | l_101.edges = (q_6 -> q_14) &&
	let l_102 = l_101.next | l_102.edges = (q_6 -> q_15) &&
	let l_103 = l_102.next | l_103.edges = (q_6 -> q_16) &&
	let l_104 = l_103.next | l_104.edges = (q_6 -> q_17) &&
	let l_105 = l_104.next | l_105.edges = (q_6 -> q_18) &&
	let l_106 = l_105.next | l_106.edges = (q_6 -> q_19) +
                                               (q_7 -> q_8) &&
	let l_107 = l_106.next | l_107.edges = (q_7 -> q_9) &&
	let l_108 = l_107.next | l_108.edges = (q_7 -> q_10) &&
	let l_109 = l_108.next | l_109.edges = (q_7 -> q_11) &&
	let l_110 = l_109.next | l_110.edges = (q_7 -> q_12) 
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
