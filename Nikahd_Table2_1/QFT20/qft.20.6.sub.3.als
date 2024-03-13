
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
		(q_0 -> M_0) + 
		(q_1 -> M_3) + 
		(q_2 -> M_0) + 
		(q_3 -> M_0) + 
		(q_4 -> M_0) + 
		(q_5 -> M_1) + 
		(q_6 -> M_1) + 
		(q_7 -> M_1) + 
		(q_8 -> M_2) + 
		(q_9 -> M_2) + 
		(q_10 -> M_2) + 
		(q_11 -> M_3) + 
		(q_12 -> M_3) + 
		(q_13 -> M_3) + 
		(q_14 -> M_2) + 
		(q_15 -> M_4) + 
		(q_16 -> M_4) + 
		(q_17 -> M_4) + 
		(q_18 -> M_4) + 
		(q_19 -> M_1) &&

	let l_31 = l_0.next   | l_31.edges  = (q_1 -> q_14) &&
	let l_32 = l_31.next   | l_32.edges  = (q_1 -> q_15) &&
	let l_33 = l_32.next   | l_33.edges  = (q_1 -> q_16) &&
	let l_34 = l_33.next   | l_34.edges  = (q_1 -> q_17) &&
	let l_35 = l_34.next   | l_35.edges  = (q_1 -> q_18) &&
	let l_36 = l_35.next   | l_36.edges  = (q_1 -> q_19) +
                                               (q_2 -> q_3) &&
	let l_37 = l_36.next   | l_37.edges  = (q_2 -> q_4) &&
	let l_38 = l_37.next   | l_38.edges  = (q_2 -> q_5) &&
	let l_39 = l_38.next   | l_39.edges  = (q_2 -> q_6) &&
	let l_40 = l_39.next   | l_40.edges  = (q_2 -> q_7) 
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
