
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_a, q_b, q_E, q_c, q_d, q_e extends Qubit { }

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
	#(c.location).M_0 < 4 &&
	#(c.location).M_1 < 4
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 4 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =

		(q_a -> M_1) + 
		(q_b -> M_0) + 
		(q_E -> M_0) + 
		(q_c -> M_0) + 
		(q_d -> M_1) + 
		(q_e -> M_1)  &&

	let l_1 = l_0.next   | l_1.edges  = (q_a -> q_E) + (q_E -> q_c) &&
	let l_2 = l_1.next   | l_2.edges  = (q_b -> q_d) + (q_d -> q_E) &&
	let l_3 = l_2.next   | l_3.edges  = (q_b -> q_e) + (q_e -> q_c)

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
    lte[grph/last.numTele, 3]
}

run finalLayer for 4 circGraph, 6 Int
