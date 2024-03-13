
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
		(q_4 -> M_0) + 
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
		(q_19 -> M_2) &&

	let l_71 = l_0.next   | l_71.edges  = (q_4 -> q_9) &&
	let l_72 = l_71.next   | l_72.edges  = (q_4 -> q_10) &&
	let l_73 = l_72.next   | l_73.edges  = (q_4 -> q_11) &&
	let l_74 = l_73.next   | l_74.edges  = (q_4 -> q_12) &&
	let l_75 = l_74.next   | l_75.edges  = (q_4 -> q_13) &&
	let l_76 = l_75.next   | l_76.edges  = (q_4 -> q_14) &&
	let l_77 = l_76.next   | l_77.edges  = (q_4 -> q_15) &&
	let l_78 = l_77.next   | l_78.edges  = (q_4 -> q_16) &&
	let l_79 = l_78.next   | l_79.edges  = (q_4 -> q_17) &&
	let l_80 = l_79.next   | l_80.edges  = (q_4 -> q_18) 
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
