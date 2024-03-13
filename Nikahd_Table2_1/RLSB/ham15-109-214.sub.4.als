
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_a, q_b, q_c, q_d, q_e, q_f, q_g, q_h, q_i, q_j, q_k, q_l, q_m, q_n, q_o extends Qubit { }

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
	#(c.location).M_0 < 6 &&
	#(c.location).M_1 < 6 &&
	#(c.location).M_2 < 6
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 6 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_a -> M_2) + 
		(q_b -> M_2) + 
		(q_c -> M_2) + 
		(q_d -> M_2) + 
		(q_e -> M_2) + 
		(q_f -> M_1) + 
		(q_g -> M_1) + 
		(q_h -> M_1) + 
		(q_i -> M_0) + 
		(q_j -> M_1) + 
		(q_k -> M_0) + 
		(q_l -> M_0) + 
		(q_m -> M_1) + 
		(q_n -> M_0) + 
		(q_o -> M_0) &&

	let l_73 = l_0.next | l_73.edges = (q_f -> q_j) &&
	let l_74 = l_73.next | l_74.edges = (q_f -> q_i) &&
	let l_75 = l_74.next | l_75.edges = (q_i -> q_e) &&
	let l_76 = l_75.next | l_76.edges = (q_e -> q_i) &&
	let l_77 = l_76.next | l_77.edges = (q_e -> q_h) &&
	let l_78 = l_77.next | l_78.edges = (q_h -> q_d) &&
	let l_79 = l_78.next | l_79.edges = (q_d -> q_h) &&
	let l_80 = l_79.next | l_80.edges = (q_d -> q_g) &&
	let l_81 = l_80.next | l_81.edges = (q_g -> q_c) &&
	let l_82 = l_81.next | l_82.edges = (q_c -> q_g) &&
	let l_83 = l_82.next | l_83.edges = (q_c -> q_f) &&
	let l_84 = l_83.next | l_84.edges = (q_f -> q_b) &&
	let l_85 = l_84.next | l_85.edges = (q_b -> q_f) &&
	let l_86 = l_85.next | l_86.edges = (q_b -> q_e) &&
	let l_87 = l_86.next | l_87.edges = (q_e -> q_a) &&
	let l_88 = l_87.next | l_88.edges = (q_a -> q_e) &&
	let l_89 = l_88.next | l_89.edges = (q_a -> q_d)

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
    lte[grph/last.numTele, 168]
}

run finalLayer for 18 circGraph, 12 Int
