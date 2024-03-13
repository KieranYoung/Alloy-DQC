
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
		(q_0 -> M_1) + 
		(q_1 -> M_0) + 
		(q_2 -> M_0) + 
		(q_3 -> M_0) + 
		(q_4 -> M_0) + 
		(q_5 -> M_0) + 
		(q_6 -> M_0) + 
		(q_7 -> M_1) + 
		(q_8 -> M_1) + 
		(q_9 -> M_1) + 
		(q_10 -> M_1) + 
		(q_11 -> M_1) + 
		(q_12 -> M_1) + 
		(q_13 -> M_2) + 
		(q_14 -> M_2) + 
		(q_15 -> M_2) + 
		(q_16 -> M_2) + 
		(q_17 -> M_2) + 
		(q_18 -> M_2) + 
		(q_19 -> M_2) &&

	let l_11 = l_0.next   | l_11.edges  = (q_0 -> q_11) &&
	let l_12 = l_11.next   | l_12.edges  = (q_0 -> q_12) &&
	let l_13 = l_12.next   | l_13.edges  = (q_0 -> q_13) &&
	let l_14 = l_13.next   | l_14.edges  = (q_0 -> q_14) &&
	let l_15 = l_14.next   | l_15.edges  = (q_0 -> q_15) &&
	let l_16 = l_15.next   | l_16.edges  = (q_0 -> q_16) &&
	let l_17 = l_16.next   | l_17.edges  = (q_0 -> q_17) &&
	let l_18 = l_17.next   | l_18.edges  = (q_0 -> q_18) &&
	let l_19 = l_18.next   | l_19.edges  = (q_0 -> q_19) +
                                               (q_1 -> q_2) &&
	let l_20 = l_19.next   | l_20.edges  = (q_1 -> q_3) 
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
