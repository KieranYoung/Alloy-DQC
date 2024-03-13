
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_a, q_b, q_c, q_d, q_e extends Qubit { }

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

		(q_a -> M_0) + 
		(q_b -> M_1) + 
		(q_c -> M_1) + 
		(q_d -> M_0) + 
		(q_e -> M_0)  &&

	let l_1 = l_0.next   | l_1.edges  = (q_a -> q_b) + (q_b -> q_e) &&
	let l_2 = l_1.next   | l_2.edges  = (q_a -> q_c) + (q_c -> q_e) &&
	let l_3 = l_2.next   | l_3.edges  = (q_b -> q_c) + (q_c -> q_e) +
                                            (q_a -> q_d) &&
	let l_4 = l_3.next   | l_4.edges  = (q_b -> q_d) &&
	let l_5 = l_4.next   | l_5.edges  = (q_c -> q_d)

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

run finalLayer for 6 circGraph, 6 Int
