
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_x0, q_x1, q_x2, q_x3, q_x4, q_x5, q_x6, q_x7, q_x8, q_x9, q_x10, q_x11, q_x12, q_x13 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3, M_4 extends Machine { }

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
	#(c.location).M_1 < 4 &&
	#(c.location).M_2 < 4 &&
	#(c.location).M_3 < 4 &&
	#(c.location).M_4 < 4
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 4 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_x0 -> M_0) + 
		(q_x1 -> M_0) + 
		(q_x2 -> M_0) + 
		(q_x3 -> M_1) + 
		(q_x4 -> M_1) + 
		(q_x5 -> M_1) + 
		(q_x6 -> M_2) + 
		(q_x7 -> M_2) + 
		(q_x8 -> M_2) + 
		(q_x9 -> M_3) + 
		(q_x10 -> M_3) + 
		(q_x11 -> M_3) + 
		(q_x12 -> M_4) + 
		(q_x13 -> M_4) &&
	let l_1 = l_0.next   | l_1.edges  = (q_x4 -> q_x3) +
                                            (q_x6 -> q_x5) +
                                            (q_x8 -> q_x7) +
                                            (q_x10 -> q_x9) +
                                            (q_x12 -> q_x11) &&
	let l_2 = l_1.next   | l_2.edges  = (q_x4 -> q_x2) &&
	let l_3 = l_2.next   | l_3.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) +
                                            (q_x6 -> q_x4) &&
	let l_4 = l_3.next   | l_4.edges  = (q_x2 -> q_x3) + (q_x3 -> q_x4) +
                                            (q_x8 -> q_x6) &&
	let l_5 = l_4.next   | l_5.edges  = (q_x4 -> q_x5) + (q_x5 -> q_x6) +
                                            (q_x10 -> q_x8) &&
	let l_6 = l_5.next   | l_6.edges  = (q_x6 -> q_x7) + (q_x7 -> q_x8) +
                                            (q_x12 -> q_x10) &&
	let l_7 = l_6.next   | l_7.edges  = (q_x8 -> q_x9) + (q_x9 -> q_x10) +
                                            (q_x12 -> q_x13) &&
	let l_8 = l_7.next   | l_8.edges  = (q_x10 -> q_x11) + (q_x11 -> q_x13) +
                                            (q_x2 -> q_x3) +
                                            (q_x4 -> q_x5) +
                                            (q_x6 -> q_x7) +
                                            (q_x8 -> q_x9) &&
	let l_9 = l_8.next   | l_9.edges  = (q_x10 -> q_x11) &&
	let l_10 = l_9.next  | l_10.edges = (q_x8 -> q_x9) + (q_x9 -> q_x10) &&
	let l_11 = l_10.next | l_11.edges = (q_x6 -> q_x7) + (q_x7 -> q_x8) +
                                            (q_x12 -> q_x10) &&
	let l_12 = l_11.next | l_12.edges = (q_x4 -> q_x5) + (q_x5 -> q_x6) +
                                            (q_x10 -> q_x8) &&
	let l_13 = l_12.next | l_13.edges = (q_x2 -> q_x3) + (q_x3 -> q_x4) +
                                            (q_x8 -> q_x6) &&
	let l_14 = l_13.next | l_14.edges = (q_x0 -> q_x1) + (q_x1 -> q_x2) +
                                            (q_x6 -> q_x4) &&
	let l_15 = l_14.next | l_15.edges = (q_x4 -> q_x2) +
                                            (q_x1 -> q_x0) &&
	let l_16 = l_15.next | l_16.edges = (q_x4 -> q_x3) +
                                            (q_x6 -> q_x5) +
                                            (q_x8 -> q_x7) +
                                            (q_x10 -> q_x9) +
                                            (q_x12 -> q_x11)
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
    lte[grph/last.numTele, 29]
}

run finalLayer for 17 circGraph, 9 Int
