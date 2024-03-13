
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
		(q_c -> M_1) + 
		(q_d -> M_0) + 
		(q_e -> M_2) + 
		(q_f -> M_0) + 
		(q_g -> M_0) + 
		(q_h -> M_2) + 
		(q_i -> M_0) + 
		(q_j -> M_1) + 
		(q_k -> M_2) + 
		(q_l -> M_1) + 
		(q_m -> M_1) + 
		(q_n -> M_0) + 
		(q_o -> M_2)  &&

	let l_1 = l_0.next   | l_1.edges  = (q_n -> q_l) +
                                            (q_k -> q_a) &&
	let l_2 = l_1.next   | l_2.edges  = (q_k -> q_f) &&
	let l_3 = l_2.next   | l_3.edges  = (q_k -> q_g) &&
	let l_4 = l_3.next   | l_4.edges  = (q_k -> q_h) +
                                            (q_l -> q_n) +
                                            (q_m -> q_i) &&
	let l_5 = l_4.next   | l_5.edges  = (q_m -> q_l) +
                                            (q_i -> q_h) &&
	let l_6 = l_5.next   | l_6.edges  = (q_i -> q_e) &&
	let l_7 = l_6.next   | l_7.edges  = (q_l -> q_m) + (q_m -> q_i) &&
	let l_8 = l_7.next   | l_8.edges  = (q_i -> q_e) &&
	let l_9 = l_8.next   | l_9.edges  = (q_i -> q_h) +
                                            (q_o -> q_a) &&
	let l_10 = l_9.next  | l_10.edges = (q_o -> q_g) &&
	let l_11 = l_10.next | l_11.edges = (q_o -> q_i) &&
	let l_12 = l_11.next | l_12.edges = (q_o -> q_n) +
                                            (q_m -> q_d) &&
	let l_13 = l_12.next | l_13.edges = (q_n -> q_o) + (q_o -> q_m) &&
	let l_14 = l_13.next | l_14.edges = (q_m -> q_n) &&
	let l_15 = l_14.next | l_15.edges = (q_m -> q_d) &&
	let l_16 = l_15.next | l_16.edges = (q_m -> q_n) + (q_n -> q_o) &&
	let l_17 = l_16.next | l_17.edges = (q_m -> q_k) &&
	let l_18 = l_17.next | l_18.edges = (q_n -> q_o) + (q_o -> q_m) +
                                            (q_k -> q_i) 
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
