
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
		(q_i -> M_1) + 
		(q_j -> M_1) + 
		(q_k -> M_0) + 
		(q_l -> M_0) + 
		(q_m -> M_0) + 
		(q_n -> M_0) + 
		(q_o -> M_0) &&

	let l_37 = l_0.next | l_37.edges = (q_l -> q_m) &&
	let l_38 = l_37.next | l_38.edges = (q_l -> q_f) +
                                            (q_m -> q_j) +
                                            (q_n -> q_e) &&
	let l_39 = l_38.next | l_39.edges = (q_n -> q_d) &&
	let l_40 = l_39.next | l_40.edges = (q_n -> q_c) &&
	let l_41 = l_40.next | l_41.edges = (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_n) &&
	let l_42 = l_41.next | l_42.edges = (q_n -> q_k) &&
	let l_43 = l_42.next | l_43.edges = (q_k -> q_a) &&
	let l_44 = l_43.next | l_44.edges = (q_k -> q_i) +
                                            (q_n -> q_d) &&
	let l_45 = l_44.next | l_45.edges = (q_n -> q_c) &&
	let l_46 = l_45.next | l_46.edges = (q_m -> q_c) &&
	let l_47 = l_46.next | l_47.edges = (q_m -> q_a) &&
	let l_48 = l_47.next | l_48.edges = (q_l -> q_o) + (q_o -> q_m) &&
	let l_49 = l_48.next | l_49.edges = (q_m -> q_h) &&
	let l_50 = l_49.next | l_50.edges = (q_m -> q_c) +
                                            (q_o -> q_n) &&
	let l_51 = l_50.next | l_51.edges = (q_n -> q_e) +
                                            (q_o -> q_k) &&
	let l_52 = l_51.next | l_52.edges = (q_k -> q_h) +
                                            (q_o -> q_g) &&
	let l_53 = l_52.next | l_53.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) &&
	let l_54 = l_53.next | l_54.edges = (q_o -> q_m) 
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
