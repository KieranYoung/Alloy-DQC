
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1 extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
	#(c.location).M_0 < 11 &&
	#(c.location).M_1 < 11
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 11 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_0) + 
		(q_1 -> M_0) + 
		(q_2 -> M_1) + 
		(q_3 -> M_0) + 
		(q_4 -> M_0) + 
		(q_5 -> M_0) + 
		(q_6 -> M_0) + 
		(q_7 -> M_0) + 
		(q_8 -> M_0) + 
		(q_9 -> M_0) + 
		(q_10 -> M_0) + 
		(q_11 -> M_1) + 
		(q_12 -> M_1) + 
		(q_13 -> M_1) + 
		(q_14 -> M_1) + 
		(q_15 -> M_1) + 
		(q_16 -> M_1) + 
		(q_17 -> M_1) + 
		(q_18 -> M_1) + 
		(q_19 -> M_1) &&

	let l_51 = l_0.next   | l_51.edges  = (q_2 -> q_18) &&
	let l_52 = l_51.next   | l_52.edges  = (q_2 -> q_19) +
                                               (q_3 -> q_4) &&
	let l_53 = l_52.next   | l_53.edges  = (q_3 -> q_5) &&
	let l_54 = l_53.next   | l_54.edges  = (q_3 -> q_6) &&
	let l_55 = l_54.next   | l_55.edges  = (q_3 -> q_7) &&
	let l_56 = l_55.next   | l_56.edges  = (q_3 -> q_8) &&
	let l_57 = l_56.next   | l_57.edges  = (q_3 -> q_9) &&
	let l_58 = l_57.next   | l_58.edges  = (q_3 -> q_10) &&
	let l_59 = l_58.next   | l_59.edges  = (q_3 -> q_11) &&
	let l_60 = l_59.next   | l_60.edges  = (q_3 -> q_12) 
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
