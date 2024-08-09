
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5 extends Qubit { }

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
	#(c.location).M_0 < 3 &&
	#(c.location).M_1 < 3 &&
	#(c.location).M_2 < 3
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 3 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_2) + 
		(q_1 -> M_2) + 
		(q_2 -> M_1) + 
		(q_3 -> M_0) + 
		(q_4 -> M_0) + 
		(q_5 -> M_1) &&

	let l_13 = l_0.next | l_13.edges = (q_3 -> q_4) &&
	let l_14 = l_13.next | l_14.edges = (q_3 -> q_5) 
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
    lte[grph/last.numTele, 12]
}

run finalLayer for 4 circGraph, 8 Int
