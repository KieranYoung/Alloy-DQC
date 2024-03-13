
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19, q_20, q_21, q_22, q_23, q_24, q_25, q_26, q_27, q_28, q_29, q_30, q_31, q_32, q_33, q_34, q_35, q_36, q_37, q_38, q_39, q_40, q_41, q_42, q_43, q_44, q_45, q_46, q_47, q_48, q_49, q_50, q_51, q_52, q_53, q_54, q_55, q_56, q_57, q_58, q_59, q_60, q_61, q_62, q_63 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3, M_4, M_5 extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
	#(c.location).M_0 < 12 &&
	#(c.location).M_1 < 12 &&
	#(c.location).M_2 < 12 &&
	#(c.location).M_3 < 12 &&
	#(c.location).M_4 < 12 &&
	#(c.location).M_5 < 12
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 12 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_0) + 
		(q_1 -> M_2) + 
		(q_2 -> M_0) + 
		(q_3 -> M_4) + 
		(q_4 -> M_0) + 
		(q_5 -> M_0) + 
		(q_6 -> M_0) + 
		(q_7 -> M_0) + 
		(q_8 -> M_0) + 
		(q_9 -> M_3) + 
		(q_10 -> M_4) + 
		(q_11 -> M_0) + 
		(q_12 -> M_0) + 
		(q_13 -> M_0) + 
		(q_14 -> M_2) + 
		(q_15 -> M_0) + 
		(q_16 -> M_1) + 
		(q_17 -> M_1) + 
		(q_18 -> M_1) + 
		(q_19 -> M_4) + 
		(q_20 -> M_1) + 
		(q_21 -> M_5) + 
		(q_22 -> M_2) + 
		(q_23 -> M_4) + 
		(q_24 -> M_5) + 
		(q_25 -> M_1) + 
		(q_26 -> M_1) + 
		(q_27 -> M_5) + 
		(q_28 -> M_5) + 
		(q_29 -> M_1) + 
		(q_30 -> M_1) + 
		(q_31 -> M_5) + 
		(q_32 -> M_5) + 
		(q_33 -> M_5) + 
		(q_34 -> M_3) + 
		(q_35 -> M_1) + 
		(q_36 -> M_1) + 
		(q_37 -> M_2) + 
		(q_38 -> M_2) + 
		(q_39 -> M_2) + 
		(q_40 -> M_2) + 
		(q_41 -> M_2) + 
		(q_42 -> M_2) + 
		(q_43 -> M_2) + 
		(q_44 -> M_3) + 
		(q_45 -> M_3) + 
		(q_46 -> M_3) + 
		(q_47 -> M_3) + 
		(q_48 -> M_4) + 
		(q_49 -> M_4) + 
		(q_50 -> M_4) + 
		(q_51 -> M_4) + 
		(q_52 -> M_4) + 
		(q_53 -> M_4) + 
		(q_54 -> M_4) + 
		(q_55 -> M_3) + 
		(q_56 -> M_5) + 
		(q_57 -> M_3) + 
		(q_58 -> M_3) + 
		(q_59 -> M_3) + 
		(q_60 -> M_3) + 
		(q_61 -> M_5) + 
		(q_62 -> M_5) + 
		(q_63 -> M_5) &&

	let l_1561 = l_0.next | l_1561.edges = (q_34 -> q_48) &&
	let l_1562 = l_1561.next | l_1562.edges = (q_34 -> q_49) &&
	let l_1563 = l_1562.next | l_1563.edges = (q_34 -> q_50) &&
	let l_1564 = l_1563.next | l_1564.edges = (q_34 -> q_51) &&
	let l_1565 = l_1564.next | l_1565.edges = (q_34 -> q_52) 
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
    lte[grph/last.numTele, 15648]
}

run finalLayer for 6 circGraph, 18 Int
