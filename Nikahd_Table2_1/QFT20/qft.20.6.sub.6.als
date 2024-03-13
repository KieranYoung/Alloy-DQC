
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
		(q_0 -> M_2) + 
		(q_1 -> M_1) + 
		(q_2 -> M_0) + 
		(q_3 -> M_3) + 
		(q_4 -> M_1) + 
		(q_5 -> M_1) + 
		(q_6 -> M_1) + 
		(q_7 -> M_2) + 
		(q_8 -> M_2) + 
		(q_9 -> M_2) + 
		(q_10 -> M_3) + 
		(q_11 -> M_3) + 
		(q_12 -> M_3) + 
		(q_13 -> M_0) + 
		(q_14 -> M_4) + 
		(q_15 -> M_4) + 
		(q_16 -> M_4) + 
		(q_17 -> M_4) + 
		(q_18 -> M_0) + 
		(q_19 -> M_0) &&

	let l_61 = l_0.next   | l_61.edges  = (q_3 -> q_13) &&
	let l_62 = l_61.next   | l_62.edges  = (q_3 -> q_14) &&
	let l_63 = l_62.next   | l_63.edges  = (q_3 -> q_15) &&
	let l_64 = l_63.next   | l_64.edges  = (q_3 -> q_16) &&
	let l_65 = l_64.next   | l_65.edges  = (q_3 -> q_17) &&
	let l_66 = l_65.next   | l_66.edges  = (q_3 -> q_18) &&
	let l_67 = l_66.next   | l_67.edges  = (q_3 -> q_19) +
                                               (q_4 -> q_5) &&
	let l_68 = l_67.next   | l_68.edges  = (q_4 -> q_6) &&
	let l_69 = l_68.next   | l_69.edges  = (q_4 -> q_7) &&
	let l_70 = l_69.next   | l_70.edges  = (q_4 -> q_8) 
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
