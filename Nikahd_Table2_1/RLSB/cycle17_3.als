
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_a, q_b, q_c, q_d, q_e, q_f, q_g, q_h, q_i, q_j, q_k, q_l, q_m, q_n, q_o, q_p, q_q, q_r, q_s, q_t extends Qubit { }

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
	#(c.location).M_0 < 19 &&
	#(c.location).M_1 < 19
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 19 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_a -> M_0) + 
		(q_b -> M_1) + 
		(q_c -> M_1) + 
		(q_d -> M_1) + 
		(q_e -> M_0) + 
		(q_f -> M_1) + 
		(q_g -> M_1) + 
		(q_h -> M_0) + 
		(q_i -> M_0) + 
		(q_j -> M_0) + 
		(q_k -> M_1) + 
		(q_l -> M_0) + 
		(q_m -> M_1) + 
		(q_n -> M_1) + 
		(q_o -> M_1) + 
		(q_p -> M_0) + 
		(q_q -> M_0) + 
		(q_r -> M_0) + 
		(q_s -> M_1) + 
		(q_t -> M_0) &&
	let l_1 = l_0.next     | l_1.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_p) + (q_p -> q_t) + (q_t -> q_q) &&
	let l_2 = l_1.next     | l_2.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_t) + (q_t -> q_p) &&
	let l_3 = l_2.next     | l_3.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_t) + (q_t -> q_o) &&
	let l_4 = l_3.next     | l_4.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_t) + (q_t -> q_n) &&
	let l_5 = l_4.next     | l_5.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_t) + (q_t -> q_m) &&
	let l_6 = l_5.next     | l_6.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_t) + (q_t -> q_l) &&
	let l_7 = l_6.next     | l_7.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_t) + (q_t -> q_k) &&
	let l_8 = l_7.next     | l_8.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_t) + (q_t -> q_j) &&
	let l_9 = l_8.next     | l_9.edges   = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_t) + (q_t -> q_i) &&
	let l_10 = l_9.next    | l_10.edges  = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_t) + (q_t -> q_h) &&
	let l_11 = l_10.next   | l_11.edges  = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_t) + (q_t -> q_g) &&
	let l_12 = l_11.next   | l_12.edges  = (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_t) + (q_t -> q_f) &&
	let l_13 = l_12.next   | l_13.edges  = (q_c -> q_d) + (q_d -> q_t) + (q_t -> q_e) &&
	let l_14 = l_13.next   | l_14.edges  = (q_c -> q_t) + (q_t -> q_d) &&
	let l_15 = l_14.next   | l_15.edges  = (q_t -> q_c) &&
	let l_16 = l_15.next   | l_16.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_p) + (q_p -> q_s) + (q_s -> q_q) &&
	let l_17 = l_16.next   | l_17.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_s) + (q_s -> q_p) &&
	let l_18 = l_17.next   | l_18.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_s) + (q_s -> q_o) &&
	let l_19 = l_18.next   | l_19.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_s) + (q_s -> q_n) &&
	let l_20 = l_19.next   | l_20.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_s) + (q_s -> q_m) &&
	let l_21 = l_20.next   | l_21.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_s) + (q_s -> q_l) &&
	let l_22 = l_21.next   | l_22.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_s) + (q_s -> q_k) &&
	let l_23 = l_22.next   | l_23.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_s) + (q_s -> q_j) &&
	let l_24 = l_23.next   | l_24.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_s) + (q_s -> q_i) &&
	let l_25 = l_24.next   | l_25.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_s) + (q_s -> q_h) &&
	let l_26 = l_25.next   | l_26.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_s) + (q_s -> q_g) &&
	let l_27 = l_26.next   | l_27.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_s) + (q_s -> q_f) &&
	let l_28 = l_27.next   | l_28.edges  = (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_s) + (q_s -> q_e) &&
	let l_29 = l_28.next   | l_29.edges  = (q_b -> q_c) + (q_c -> q_s) + (q_s -> q_d) &&
	let l_30 = l_29.next   | l_30.edges  = (q_b -> q_s) + (q_s -> q_c) &&
	let l_31 = l_30.next   | l_31.edges  = (q_s -> q_b) &&
	let l_32 = l_31.next   | l_32.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_p) + (q_p -> q_r) + (q_r -> q_q) &&
	let l_33 = l_32.next   | l_33.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_r) + (q_r -> q_p) &&
	let l_34 = l_33.next   | l_34.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_r) + (q_r -> q_o) &&
	let l_35 = l_34.next   | l_35.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_r) + (q_r -> q_n) &&
	let l_36 = l_35.next   | l_36.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_r) + (q_r -> q_m) &&
	let l_37 = l_36.next   | l_37.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_k) + (q_k -> q_r) + (q_r -> q_l) &&
	let l_38 = l_37.next   | l_38.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_j) + (q_j -> q_r) + (q_r -> q_k) &&
	let l_39 = l_38.next   | l_39.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_i) + (q_i -> q_r) + (q_r -> q_j) &&
	let l_40 = l_39.next   | l_40.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_h) + (q_h -> q_r) + (q_r -> q_i) &&
	let l_41 = l_40.next   | l_41.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_g) + (q_g -> q_r) + (q_r -> q_h) &&
	let l_42 = l_41.next   | l_42.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_f) + (q_f -> q_r) + (q_r -> q_g) &&
	let l_43 = l_42.next   | l_43.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_e) + (q_e -> q_r) + (q_r -> q_f) &&
	let l_44 = l_43.next   | l_44.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_d) + (q_d -> q_r) + (q_r -> q_e) &&
	let l_45 = l_44.next   | l_45.edges  = (q_a -> q_b) + (q_b -> q_c) + (q_c -> q_r) + (q_r -> q_d) &&
	let l_46 = l_45.next   | l_46.edges  = (q_a -> q_b) + (q_b -> q_r) + (q_r -> q_c) &&
	let l_47 = l_46.next   | l_47.edges  = (q_a -> q_r) + (q_r -> q_b) &&
	let l_48 = l_47.next   | l_48.edges  = (q_r -> q_a)
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
    lte[grph/last.numTele, 122]
}

run finalLayer for 49 circGraph, 11 Int
