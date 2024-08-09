
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_f6, q_f5, q_f4, q_f3, q_f2, q_f1, q_f0, q_x7, q_x6, q_x5, q_x4, q_x3, q_x2, q_x1, q_x0 extends Qubit { }

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
	#(c.location).M_0 < 9 &&
	#(c.location).M_1 < 9
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 9 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_f6 -> M_0) + 
		(q_f5 -> M_0) + 
		(q_f4 -> M_0) + 
		(q_f3 -> M_0) + 
		(q_f2 -> M_0) + 
		(q_f1 -> M_0) + 
		(q_f0 -> M_0) + 
		(q_x7 -> M_0) + 
		(q_x6 -> M_1) + 
		(q_x5 -> M_1) + 
		(q_x4 -> M_1) + 
		(q_x3 -> M_1) + 
		(q_x2 -> M_1) + 
		(q_x1 -> M_1) + 
		(q_x0 -> M_1) &&
	let l_1 = l_0.next     | l_1.edges   = (q_x7 -> q_f6) +
                                               (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f0) &&
	let l_2 = l_1.next     | l_2.edges   = (q_x0 -> q_x4) + (q_x4 -> q_x6) + (q_x6 -> q_f5) &&
	let l_3 = l_2.next     | l_3.edges   = (q_x0 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_f4) &&
	let l_4 = l_3.next     | l_4.edges   = (q_x0 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_f1) &&
	let l_5 = l_4.next     | l_5.edges   = (q_x0 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_f3) &&
	let l_6 = l_5.next     | l_6.edges   = (q_x0 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_f4) &&
	let l_7 = l_6.next     | l_7.edges   = (q_x0 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f3) &&
	let l_8 = l_7.next     | l_8.edges   = (q_x0 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f4) &&
	let l_9 = l_8.next     | l_9.edges   = (q_x0 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f5) &&
	let l_10 = l_9.next    | l_10.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_f1) &&
	let l_11 = l_10.next   | l_11.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_f3) &&
	let l_12 = l_11.next   | l_12.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_f1) &&
	let l_13 = l_12.next   | l_13.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_f2) &&
	let l_14 = l_13.next   | l_14.edges  = (q_x0 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3) &&
	let l_15 = l_14.next   | l_15.edges  = (q_x0 -> q_x3) + (q_x3 -> q_f2) &&
	let l_16 = l_15.next   | l_16.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f2) &&
	let l_17 = l_16.next   | l_17.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f2) &&
	let l_18 = l_17.next   | l_18.edges  = (q_x0 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f1) &&
	let l_19 = l_18.next   | l_19.edges  = (q_x0 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f3) &&
	let l_20 = l_19.next   | l_20.edges  = (q_x0 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_f3) &&
	let l_21 = l_20.next   | l_21.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_f0) &&
	let l_22 = l_21.next   | l_22.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_f1) &&
	let l_23 = l_22.next   | l_23.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_f2) &&
	let l_24 = l_23.next   | l_24.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f3) &&
	let l_25 = l_24.next   | l_25.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_f0) &&
	let l_26 = l_25.next   | l_26.edges  = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f2) &&
	let l_27 = l_26.next   | l_27.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x6) + (q_x6 -> q_f4) &&
	let l_28 = l_27.next   | l_28.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f2) &&
	let l_29 = l_28.next   | l_29.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f3) &&
	let l_30 = l_29.next   | l_30.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_f5) &&
	let l_31 = l_30.next   | l_31.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_x6) + (q_x6 -> q_f5) &&
	let l_32 = l_31.next   | l_32.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_f4) &&
	let l_33 = l_32.next   | l_33.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f1) &&
	let l_34 = l_33.next   | l_34.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3) &&
	let l_35 = l_34.next   | l_35.edges  = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f2) &&
	let l_36 = l_35.next   | l_36.edges  = (q_x1 -> q_x2) + (q_x2 -> q_f2) +
                                               (q_x0 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x6) + (q_x6 -> q_f4) &&
	let l_37 = l_36.next   | l_37.edges  = (q_x0 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f2) &&
	let l_38 = l_37.next   | l_38.edges  = (q_x0 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f5) &&
	let l_39 = l_38.next   | l_39.edges  = (q_x0 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3) &&
	let l_40 = l_39.next   | l_40.edges  = (q_x0 -> q_x2) + (q_x2 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f4) &&
	let l_41 = l_40.next   | l_41.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f2) &&
	let l_42 = l_41.next   | l_42.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3) &&
	let l_43 = l_42.next   | l_43.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x3) + (q_x3 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3) &&
	let l_44 = l_43.next   | l_44.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f0) &&
	let l_45 = l_44.next   | l_45.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f2) &&
	let l_46 = l_45.next   | l_46.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3) &&
	let l_47 = l_46.next   | l_47.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f1) &&
	let l_48 = l_47.next   | l_48.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f2) &&
	let l_49 = l_48.next   | l_49.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3) &&
	let l_50 = l_49.next   | l_50.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f1) &&
	let l_51 = l_50.next   | l_51.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f5) &&
	let l_52 = l_51.next   | l_52.edges  = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_x4) + (q_x4 -> q_x5) + (q_x5 -> q_x6) + (q_x6 -> q_f3)
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
    lte[grph/last.numTele, 99]
}

run finalLayer for 53 circGraph, 11 Int
