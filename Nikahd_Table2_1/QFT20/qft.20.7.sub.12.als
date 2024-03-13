
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3, M_4, M_5, M_6 extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
	#(c.location).M_0 < 4 &&
	#(c.location).M_1 < 4 &&
	#(c.location).M_2 < 4 &&
	#(c.location).M_3 < 4 &&
	#(c.location).M_4 < 4 &&
	#(c.location).M_5 < 4 &&
	#(c.location).M_6 < 4
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 4 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_0) + 
		(q_1 -> M_4) + 
		(q_2 -> M_4) + 
		(q_3 -> M_4) + 
		(q_4 -> M_0) + 
		(q_5 -> M_3) + 
		(q_6 -> M_5) + 
		(q_7 -> M_6) + 
		(q_8 -> M_1) + 
		(q_9 -> M_2) + 
		(q_10 -> M_2) + 
		(q_11 -> M_1) + 
		(q_12 -> M_1) + 
		(q_13 -> M_0) + 
		(q_14 -> M_3) + 
		(q_15 -> M_3) + 
		(q_16 -> M_5) + 
		(q_17 -> M_5) + 
		(q_18 -> M_6) + 
		(q_19 -> M_6) &&

	let l_120 = l_0.next | l_120.edges = (q_8 -> q_12) &&
	let l_121 = l_120.next | l_121.edges = (q_8 -> q_13) &&
	let l_122 = l_121.next | l_122.edges = (q_8 -> q_14) &&
	let l_123 = l_122.next | l_123.edges = (q_8 -> q_15) &&
	let l_124 = l_123.next | l_124.edges = (q_8 -> q_16) &&
	let l_125 = l_124.next | l_125.edges = (q_8 -> q_17) &&
	let l_126 = l_125.next | l_126.edges = (q_8 -> q_18) &&
	let l_127 = l_126.next | l_127.edges = (q_8 -> q_19) +
                                               (q_9 -> q_10) &&
	let l_128 = l_127.next | l_128.edges = (q_9 -> q_11) 
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
