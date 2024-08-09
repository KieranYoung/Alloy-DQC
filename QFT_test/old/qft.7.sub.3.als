
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6 extends Qubit { }

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
	#(c.location).M_0 < 3 &&
	#(c.location).M_1 < 3 &&
	#(c.location).M_2 < 3 &&
	#(c.location).M_3 < 3
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 3 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_3) + 
		(q_1 -> M_3) + 
		(q_2 -> M_2) + 
		(q_3 -> M_0) + 
		(q_4 -> M_0) + 
		(q_5 -> M_1) + 
		(q_6 -> M_1) &&

	let l_16 = l_0.next | l_16.edges = (q_3 -> q_4) &&
	let l_17 = l_16.next | l_17.edges = (q_3 -> q_5) &&
	let l_18 = l_17.next | l_18.edges = (q_3 -> q_6) &&
	let l_19 = l_18.next | l_19.edges = (q_4 -> q_5) &&
	let l_20 = l_19.next | l_20.edges = (q_4 -> q_6) &&
	let l_21 = l_20.next | l_21.edges = (q_5 -> q_6)

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
    lte[grph/last.numTele, 19]
}

run finalLayer for 8 circGraph, 9 Int
