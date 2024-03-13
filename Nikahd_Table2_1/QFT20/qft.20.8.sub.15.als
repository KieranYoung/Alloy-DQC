
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
		(q_5 -> M_0) + 
		(q_6 -> M_1) + 
		(q_7 -> M_1) + 
		(q_8 -> M_1) + 
		(q_9 -> M_5) + 
		(q_10 -> M_6) + 
		(q_11 -> M_3) + 
		(q_12 -> M_2) + 
		(q_13 -> M_2) + 
		(q_14 -> M_3) + 
		(q_15 -> M_3) + 
		(q_16 -> M_5) + 
		(q_17 -> M_5) + 
		(q_18 -> M_6) + 
		(q_19 -> M_6) &&

	let l_147 = l_0.next | l_147.edges = (q_11 -> q_15) &&
	let l_148 = l_147.next | l_148.edges = (q_11 -> q_16) &&
	let l_149 = l_148.next | l_149.edges = (q_11 -> q_17) &&
	let l_150 = l_149.next | l_150.edges = (q_11 -> q_18) &&
	let l_151 = l_150.next | l_151.edges = (q_11 -> q_19) +
                                               (q_12 -> q_13) &&
	let l_152 = l_151.next | l_152.edges = (q_12 -> q_14) &&
	let l_153 = l_152.next | l_153.edges = (q_12 -> q_15) &&
	let l_154 = l_153.next | l_154.edges = (q_12 -> q_16) &&
	let l_155 = l_154.next | l_155.edges = (q_12 -> q_17) 
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
