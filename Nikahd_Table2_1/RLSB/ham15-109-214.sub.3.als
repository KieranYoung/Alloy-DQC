
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
		(q_b -> M_1) + 
		(q_c -> M_2) + 
		(q_d -> M_2) + 
		(q_e -> M_1) + 
		(q_f -> M_1) + 
		(q_g -> M_0) + 
		(q_h -> M_2) + 
		(q_i -> M_1) + 
		(q_j -> M_1) + 
		(q_k -> M_2) + 
		(q_l -> M_0) + 
		(q_m -> M_0) + 
		(q_n -> M_0) + 
		(q_o -> M_0) &&

	let l_55 = l_0.next | l_55.edges = (q_m -> q_e) &&
	let l_56 = l_55.next | l_56.edges = (q_m -> q_a) +
                                            (q_o -> q_l) &&
	let l_57 = l_56.next | l_57.edges = (q_o -> q_k) &&
	let l_58 = l_57.next | l_58.edges = (q_o -> q_g) &&
	let l_59 = l_58.next | l_59.edges = (q_l -> q_n) + (q_n -> q_o) &&
	let l_60 = l_59.next | l_60.edges = (q_o -> q_n) &&
	let l_61 = l_60.next | l_61.edges = (q_o -> q_l) &&
	let l_62 = l_61.next | l_62.edges = (q_k -> q_o) &&
	let l_63 = l_62.next | l_63.edges = (q_n -> q_k) &&
	let l_64 = l_63.next | l_64.edges = (q_k -> q_n) &&
	let l_65 = l_64.next | l_65.edges = (q_n -> q_g) &&
	let l_66 = l_65.next | l_66.edges = (q_n -> q_j) &&
	let l_67 = l_66.next | l_67.edges = (q_j -> q_n) +
                                            (q_i -> q_m) &&
	let l_68 = l_67.next | l_68.edges = (q_j -> q_i) +
                                            (q_h -> q_l) &&
	let l_69 = l_68.next | l_69.edges = (q_i -> q_h) +
                                            (q_g -> q_k) &&
	let l_70 = l_69.next | l_70.edges = (q_h -> q_g) &&
	let l_71 = l_70.next | l_71.edges = (q_g -> q_j) &&
	let l_72 = l_71.next | l_72.edges = (q_j -> q_f) 
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

run finalLayer for 19 circGraph, 12 Int
