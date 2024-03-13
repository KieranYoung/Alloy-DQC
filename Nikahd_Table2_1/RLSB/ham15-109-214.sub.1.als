
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
		(q_a -> M_1) + 
		(q_b -> M_2) + 
		(q_c -> M_2) + 
		(q_d -> M_2) + 
		(q_e -> M_1) + 
		(q_f -> M_2) + 
		(q_g -> M_1) + 
		(q_h -> M_1) + 
		(q_i -> M_0) + 
		(q_j -> M_2) + 
		(q_k -> M_0) + 
		(q_l -> M_1) + 
		(q_m -> M_0) + 
		(q_n -> M_0) + 
		(q_o -> M_0) &&

	let l_19 = l_0.next | l_19.edges = (q_k -> q_j) &&
	let l_20 = l_19.next | l_20.edges = (q_k -> q_e) &&
	let l_21 = l_20.next | l_21.edges = (q_m -> q_k) &&
	let l_22 = l_21.next | l_22.edges = (q_k -> q_d) &&
	let l_23 = l_22.next | l_23.edges = (q_k -> q_c) &&
	let l_24 = l_23.next | l_24.edges = (q_k -> q_b) &&
	let l_25 = l_24.next | l_25.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_k) &&
	let l_26 = l_25.next | l_26.edges = (q_k -> q_j) &&
	let l_27 = l_26.next | l_27.edges = (q_k -> q_g) &&
	let l_28 = l_27.next | l_28.edges = (q_k -> q_e) &&
	let l_29 = l_28.next | l_29.edges = (q_k -> q_d) &&
	let l_30 = l_29.next | l_30.edges = (q_k -> q_c) &&
	let l_31 = l_30.next | l_31.edges = (q_k -> q_b) &&
	let l_32 = l_31.next | l_32.edges = (q_l -> q_k) &&
	let l_33 = l_32.next | l_33.edges = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_l) +
                                            (q_k -> q_f) &&
	let l_34 = l_33.next | l_34.edges = (q_l -> q_k) +
                                            (q_m -> q_h) &&
	let l_35 = l_34.next | l_35.edges = (q_n -> q_k) +
                                            (q_l -> q_m) &&
	let l_36 = l_35.next | l_36.edges = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_l) 
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
