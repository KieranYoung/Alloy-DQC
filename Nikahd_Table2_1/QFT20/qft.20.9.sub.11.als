
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
		(q_2 -> M_0) + 
		(q_3 -> M_4) + 
		(q_4 -> M_3) + 
		(q_5 -> M_5) + 
		(q_6 -> M_6) + 
		(q_7 -> M_1) + 
		(q_8 -> M_4) + 
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

	let l_111 = l_0.next | l_111.edges = (q_7 -> q_13) &&
	let l_112 = l_111.next | l_112.edges = (q_7 -> q_14) &&
	let l_113 = l_112.next | l_113.edges = (q_7 -> q_15) &&
	let l_114 = l_113.next | l_114.edges = (q_7 -> q_16) &&
	let l_115 = l_114.next | l_115.edges = (q_7 -> q_17) &&
	let l_116 = l_115.next | l_116.edges = (q_7 -> q_18) &&
	let l_117 = l_116.next | l_117.edges = (q_7 -> q_19) +
                                               (q_8 -> q_9) &&
	let l_118 = l_117.next | l_118.edges = (q_8 -> q_10) &&
	let l_119 = l_118.next | l_119.edges = (q_8 -> q_11) 
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
