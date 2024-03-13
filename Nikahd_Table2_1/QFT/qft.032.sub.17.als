
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
		(q_0 -> M_2) + 
		(q_1 -> M_2) + 
		(q_2 -> M_3) + 
		(q_3 -> M_1) + 
		(q_4 -> M_0) + 
		(q_5 -> M_3) + 
		(q_6 -> M_1) + 
		(q_7 -> M_0) + 
		(q_8 -> M_0) + 
		(q_9 -> M_1) + 
		(q_10 -> M_1) + 
		(q_11 -> M_1) + 
		(q_12 -> M_1) + 
		(q_13 -> M_0) + 
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

	let l_171 = l_0.next | l_171.edges = (q_6 -> q_12) &&
	let l_172 = l_171.next | l_172.edges = (q_6 -> q_13) &&
	let l_173 = l_172.next | l_173.edges = (q_6 -> q_14) &&
	let l_174 = l_173.next | l_174.edges = (q_6 -> q_15) &&
	let l_175 = l_174.next | l_175.edges = (q_6 -> q_16) &&
	let l_176 = l_175.next | l_176.edges = (q_6 -> q_17) &&
	let l_177 = l_176.next | l_177.edges = (q_6 -> q_18) &&
	let l_178 = l_177.next | l_178.edges = (q_6 -> q_19) &&
	let l_179 = l_178.next | l_179.edges = (q_6 -> q_20) &&
	let l_180 = l_179.next | l_180.edges = (q_6 -> q_21) 
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
