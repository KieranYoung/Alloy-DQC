
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_x48, q_x47, q_x46, q_x45, q_x44, q_x43, q_x42, q_x41, q_x40, q_x39, q_x38, q_x37, q_x36, q_x35, q_x34, q_x33, q_x32, q_x31, q_x30, q_x29, q_x28, q_x27, q_x26, q_x25, q_x24, q_x23, q_x22, q_x21, q_x20, q_x19, q_x18, q_x17, q_x16, q_x15, q_x14, q_x13, q_x12, q_x11, q_x10, q_x9, q_x8, q_x7, q_x6, q_x5, q_x4, q_x3, q_x2, q_x1, q_x0 extends Qubit { }

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
	#(c.location).M_0 < 18 &&
	#(c.location).M_1 < 18 &&
	#(c.location).M_2 < 18
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 18 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =

		(q_x48 -> M_1) + 
		(q_x47 -> M_0) + 
		(q_x46 -> M_0) + 
		(q_x45 -> M_2) + 
		(q_x44 -> M_1) + 
		(q_x43 -> M_0) + 
		(q_x42 -> M_1) + 
		(q_x41 -> M_1) + 
		(q_x40 -> M_1) + 
		(q_x39 -> M_2) + 
		(q_x38 -> M_1) + 
		(q_x37 -> M_1) + 
		(q_x36 -> M_2) + 
		(q_x35 -> M_0) + 
		(q_x34 -> M_1) + 
		(q_x33 -> M_1) + 
		(q_x32 -> M_2) + 
		(q_x31 -> M_2) + 
		(q_x30 -> M_0) + 
		(q_x29 -> M_2) + 
		(q_x28 -> M_2) + 
		(q_x27 -> M_0) + 
		(q_x26 -> M_1) + 
		(q_x25 -> M_2) + 
		(q_x24 -> M_2) + 
		(q_x23 -> M_2) + 
		(q_x22 -> M_0) + 
		(q_x21 -> M_0) + 
		(q_x20 -> M_2) + 
		(q_x19 -> M_1) + 
		(q_x18 -> M_0) + 
		(q_x17 -> M_1) + 
		(q_x16 -> M_2) + 
		(q_x15 -> M_0) + 
		(q_x14 -> M_1) + 
		(q_x13 -> M_1) + 
		(q_x12 -> M_1) + 
		(q_x11 -> M_1) + 
		(q_x10 -> M_2) + 
		(q_x9 -> M_0) + 
		(q_x8 -> M_0) + 
		(q_x7 -> M_0) + 
		(q_x6 -> M_2) + 
		(q_x5 -> M_2) + 
		(q_x4 -> M_0) + 
		(q_x3 -> M_1) + 
		(q_x2 -> M_2) + 
		(q_x1 -> M_0) + 
		(q_x0 -> M_0)  &&

	let l_1 = l_0.next     | l_1.edges   = (q_x0 -> q_x1) + (q_x1 -> q_x3) &&
	let l_2 = l_1.next     | l_2.edges   = (q_x0 -> q_x1) &&
	let l_3 = l_2.next     | l_3.edges   = (q_x1 -> q_x2) + (q_x2 -> q_x3) &&
	let l_4 = l_3.next     | l_4.edges   = (q_x1 -> q_x2) +
                                               (q_x4 -> q_x5) + (q_x5 -> q_x6) &&
	let l_5 = l_4.next     | l_5.edges   = (q_x4 -> q_x5) &&
	let l_6 = l_5.next     | l_6.edges   = (q_x5 -> q_x3) + (q_x3 -> q_x6) &&
	let l_7 = l_6.next     | l_7.edges   = (q_x5 -> q_x3) +
                                               (q_x7 -> q_x8) + (q_x8 -> q_x9) &&
	let l_8 = l_7.next     | l_8.edges   = (q_x7 -> q_x8) &&
	let l_9 = l_8.next     | l_9.edges   = (q_x8 -> q_x6) + (q_x6 -> q_x9) &&
	let l_10 = l_9.next    | l_10.edges  = (q_x8 -> q_x6) +
                                               (q_x10 -> q_x11) + (q_x11 -> q_x12) 
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
    lte[grph/last.numTele, 306]
}

run finalLayer for 11 circGraph, 13 Int
