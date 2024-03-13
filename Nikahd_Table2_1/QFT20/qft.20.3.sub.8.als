
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
		(q_2 -> M_2) + 
		(q_3 -> M_2) + 
		(q_4 -> M_2) + 
		(q_5 -> M_0) + 
		(q_6 -> M_0) + 
		(q_7 -> M_0) + 
		(q_8 -> M_0) + 
		(q_9 -> M_1) + 
		(q_10 -> M_1) + 
		(q_11 -> M_1) + 
		(q_12 -> M_1) + 
		(q_13 -> M_1) + 
		(q_14 -> M_1) + 
		(q_15 -> M_2) + 
		(q_16 -> M_2) + 
		(q_17 -> M_2) + 
		(q_18 -> M_2) + 
		(q_19 -> M_0) &&

	let l_81 = l_0.next   | l_81.edges  = (q_4 -> q_19) +
                                               (q_5 -> q_6) &&
	let l_82 = l_81.next   | l_82.edges  = (q_5 -> q_7) &&
	let l_83 = l_82.next   | l_83.edges  = (q_5 -> q_8) &&
	let l_84 = l_83.next   | l_84.edges  = (q_5 -> q_9) &&
	let l_85 = l_84.next   | l_85.edges  = (q_5 -> q_10) &&
	let l_86 = l_85.next   | l_86.edges  = (q_5 -> q_11) &&
	let l_87 = l_86.next   | l_87.edges  = (q_5 -> q_12) &&
	let l_88 = l_87.next   | l_88.edges  = (q_5 -> q_13) &&
	let l_89 = l_88.next   | l_89.edges  = (q_5 -> q_14) &&
	let l_90 = l_89.next   | l_90.edges  = (q_5 -> q_15) 
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
