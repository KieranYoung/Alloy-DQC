
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
		(q_a -> M_0) + 
		(q_b -> M_0) + 
		(q_c -> M_0) + 
		(q_d -> M_0) + 
		(q_e -> M_0) + 
		(q_f -> M_1) + 
		(q_g -> M_1) + 
		(q_h -> M_1) + 
		(q_i -> M_1) + 
		(q_j -> M_1) + 
		(q_k -> M_2) + 
		(q_l -> M_2) + 
		(q_m -> M_2) + 
		(q_n -> M_2) + 
		(q_o -> M_2) &&
	let l_1 = l_0.next   | l_1.edges  = (q_o -> q_j) &&
	let l_2 = l_1.next   | l_2.edges  = (q_n -> q_o) &&
	let l_3 = l_2.next   | l_3.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_e) &&
	let l_4 = l_3.next   | l_4.edges  = (q_o -> q_l) &&
	let l_5 = l_4.next   | l_5.edges  = (q_m -> q_n) + (q_n -> q_o) &&
	let l_6 = l_5.next   | l_6.edges  = (q_l -> q_o) + (q_o -> q_n) &&
	let l_7 = l_6.next   | l_7.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_8 = l_7.next   | l_8.edges  = (q_o -> q_k) &&
	let l_9 = l_8.next   | l_9.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) &&
	let l_10 = l_9.next  | l_10.edges = (q_l -> q_o) + (q_o -> q_j) &&
	let l_11 = l_10.next | l_11.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_f) &&
	let l_12 = l_11.next | l_12.edges = (q_m -> q_o) + (q_o -> q_a) &&
	let l_13 = l_12.next | l_13.edges = (q_n -> q_o) + (q_o -> q_a) &&
	let l_14 = l_13.next | l_14.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_a) &&
	let l_15 = l_14.next | l_15.edges = (q_o -> q_m) &&
	let l_16 = l_15.next | l_16.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_d) &&
	let l_17 = l_16.next | l_17.edges = (q_m -> q_o) + (q_o -> q_j) &&
	let l_18 = l_17.next | l_18.edges = (q_m -> q_o) + (q_o -> q_c) &&
	let l_19 = l_18.next | l_19.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_c) &&
	let l_20 = l_19.next | l_20.edges = (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_n) &&
	let l_21 = l_20.next | l_21.edges = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_c) &&
	let l_22 = l_21.next | l_22.edges = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_l) &&
	let l_23 = l_22.next | l_23.edges = (q_l -> q_o) + (q_o -> q_a) &&
	let l_24 = l_23.next | l_24.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_g) &&
	let l_25 = l_24.next | l_25.edges = (q_l -> q_o) + (q_o -> q_n) &&
	let l_26 = l_25.next | l_26.edges = (q_n -> q_o) + (q_o -> q_l) &&
	let l_27 = l_26.next | l_27.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_h) &&
	let l_28 = l_27.next | l_28.edges = (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_m) &&
	let l_29 = l_28.next | l_29.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_j) &&
	let l_30 = l_29.next | l_30.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_k) &&
	let l_31 = l_30.next | l_31.edges = (q_l -> q_m) + (q_m -> q_o) &&
	let l_32 = l_31.next | l_32.edges = (q_l -> q_n) + (q_n -> q_k) &&
	let l_33 = l_32.next | l_33.edges = (q_o -> q_n) &&
	let l_34 = l_33.next | l_34.edges = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_i) &&
	let l_35 = l_34.next | l_35.edges = (q_m -> q_n) +
                                            (q_k -> q_j) &&
	let l_36 = l_35.next | l_36.edges = (q_j -> q_n) &&
	let l_37 = l_36.next | l_37.edges = (q_n -> q_m) &&
	let l_38 = l_37.next | l_38.edges = (q_m -> q_i) &&
	let l_39 = l_38.next | l_39.edges = (q_i -> q_m) +
                                            (q_l -> q_o) &&
	let l_40 = l_39.next | l_40.edges = (q_m -> q_l) &&
	let l_41 = l_40.next | l_41.edges = (q_o -> q_l) &&
	let l_42 = l_41.next | l_42.edges = (q_k -> q_o) +
                                            (q_j -> q_l) &&
	let l_43 = l_42.next | l_43.edges = (q_l -> q_h) &&
	let l_44 = l_43.next | l_44.edges = (q_h -> q_l) +
                                            (q_k -> q_n) &&
	let l_45 = l_44.next | l_45.edges = (q_h -> q_k) &&
	let l_46 = l_45.next | l_46.edges = (q_k -> q_g) &&
	let l_47 = l_46.next | l_47.edges = (q_g -> q_k) &&
	let l_48 = l_47.next | l_48.edges = (q_g -> q_j) &&
	let l_49 = l_48.next | l_49.edges = (q_j -> q_f) &&
	let l_50 = l_49.next | l_50.edges = (q_f -> q_i) &&
	let l_51 = l_50.next | l_51.edges = (q_i -> q_e) &&
	let l_52 = l_51.next | l_52.edges = (q_e -> q_h) &&
	let l_53 = l_52.next | l_53.edges = (q_h -> q_d) &&
	let l_54 = l_53.next | l_54.edges = (q_d -> q_g) &&
	let l_55 = l_54.next | l_55.edges = (q_g -> q_c) &&
	let l_56 = l_55.next | l_56.edges = (q_c -> q_g) +
                                            (q_f -> q_j) &&
	let l_57 = l_56.next | l_57.edges = (q_c -> q_f) &&
	let l_58 = l_57.next | l_58.edges = (q_f -> q_b) +
                                            (q_e -> q_i) &&
	let l_59 = l_58.next | l_59.edges = (q_b -> q_e) &&
	let l_60 = l_59.next | l_60.edges = (q_b -> q_f) +
                                            (q_e -> q_a) +
                                            (q_d -> q_h) &&
	let l_61 = l_60.next | l_61.edges = (q_a -> q_d) &&
	let l_62 = l_61.next | l_62.edges = (q_a -> q_e)
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
    lte[grph/last.numTele, 118]
}

run finalLayer for 63 circGraph, 11 Int
