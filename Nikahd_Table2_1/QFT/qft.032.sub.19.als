
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
		(q_2 -> M_0) + 
		(q_3 -> M_1) + 
		(q_4 -> M_2) + 
		(q_5 -> M_3) + 
		(q_6 -> M_3) + 
		(q_7 -> M_0) + 
		(q_8 -> M_0) + 
		(q_9 -> M_1) + 
		(q_10 -> M_1) + 
		(q_11 -> M_0) + 
		(q_12 -> M_1) + 
		(q_13 -> M_1) + 
		(q_14 -> M_1) + 
		(q_15 -> M_1) + 
		(q_16 -> M_2) + 
		(q_17 -> M_2) + 
		(q_18 -> M_2) + 
		(q_19 -> M_2) + 
		(q_20 -> M_2) + 
		(q_21 -> M_2) + 
		(q_22 -> M_0) + 
		(q_23 -> M_0) + 
		(q_24 -> M_0) + 
		(q_25 -> M_0) + 
		(q_26 -> M_3) + 
		(q_27 -> M_3) + 
		(q_28 -> M_3) + 
		(q_29 -> M_3) + 
		(q_30 -> M_3) + 
		(q_31 -> M_3) &&

	let l_191 = l_0.next | l_191.edges = (q_7 -> q_9) &&
	let l_192 = l_191.next | l_192.edges = (q_7 -> q_10) &&
	let l_193 = l_192.next | l_193.edges = (q_7 -> q_11) &&
	let l_194 = l_193.next | l_194.edges = (q_7 -> q_12) &&
	let l_195 = l_194.next | l_195.edges = (q_7 -> q_13) &&
	let l_196 = l_195.next | l_196.edges = (q_7 -> q_14) &&
	let l_197 = l_196.next | l_197.edges = (q_7 -> q_15) &&
	let l_198 = l_197.next | l_198.edges = (q_7 -> q_16) &&
	let l_199 = l_198.next | l_199.edges = (q_7 -> q_17) &&
	let l_200 = l_199.next | l_200.edges = (q_7 -> q_18) 
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
