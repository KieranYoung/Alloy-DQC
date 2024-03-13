
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_x1, q_x2, q_x3, q_x4, q_x5, q_x6, q_x7, q_x8, q_x9, q_x10, q_x11, q_x12, q_x13, q_x14, q_x15, q_x16, q_x17, q_x18, q_x19, q_x20, q_x21, q_x22, q_x23, q_x24, q_x25, q_x26, q_x27, q_x28, q_x29, q_x30, q_x31, q_x32, q_x33, q_x34, q_x35, q_x36, q_x37, q_x38, q_x39, q_x40, q_x41, q_x42, q_x43, q_x44, q_x45, q_x46, q_x47, q_x48, q_x49, q_x50, q_s1, q_s2, q_s3, q_s4, q_s5, q_s6 extends Qubit { }

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
	#(c.location).M_0 < 13 &&
	#(c.location).M_1 < 13 &&
	#(c.location).M_2 < 13 &&
	#(c.location).M_3 < 13 &&
	#(c.location).M_4 < 13
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 13 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_x1 -> M_3) + 
		(q_x2 -> M_0) + 
		(q_x3 -> M_3) + 
		(q_x4 -> M_0) + 
		(q_x5 -> M_0) + 
		(q_x6 -> M_3) + 
		(q_x7 -> M_0) + 
		(q_x8 -> M_3) + 
		(q_x9 -> M_2) + 
		(q_x10 -> M_4) + 
		(q_x11 -> M_2) + 
		(q_x12 -> M_4) + 
		(q_x13 -> M_1) + 
		(q_x14 -> M_1) + 
		(q_x15 -> M_1) + 
		(q_x16 -> M_1) + 
		(q_x17 -> M_1) + 
		(q_x18 -> M_1) + 
		(q_x19 -> M_1) + 
		(q_x20 -> M_1) + 
		(q_x21 -> M_1) + 
		(q_x22 -> M_2) + 
		(q_x23 -> M_0) + 
		(q_x24 -> M_2) + 
		(q_x25 -> M_4) + 
		(q_x26 -> M_0) + 
		(q_x27 -> M_0) + 
		(q_x28 -> M_0) + 
		(q_x29 -> M_0) + 
		(q_x30 -> M_4) + 
		(q_x31 -> M_4) + 
		(q_x32 -> M_4) + 
		(q_x33 -> M_4) + 
		(q_x34 -> M_4) + 
		(q_x35 -> M_4) + 
		(q_x36 -> M_0) + 
		(q_x37 -> M_1) + 
		(q_x38 -> M_4) + 
		(q_x39 -> M_2) + 
		(q_x40 -> M_2) + 
		(q_x41 -> M_2) + 
		(q_x42 -> M_2) + 
		(q_x43 -> M_2) + 
		(q_x44 -> M_2) + 
		(q_x45 -> M_3) + 
		(q_x46 -> M_4) + 
		(q_x47 -> M_3) + 
		(q_x48 -> M_0) + 
		(q_x49 -> M_3) + 
		(q_x50 -> M_3) + 
		(q_s1 -> M_1) + 
		(q_s2 -> M_1) + 
		(q_s3 -> M_3) + 
		(q_s4 -> M_3) + 
		(q_s5 -> M_3) + 
		(q_s6 -> M_3) &&

	let l_302 = l_0.next   | l_302.edges  = (q_s2 -> q_x21) + (q_x21 -> q_x23) &&
	let l_303 = l_302.next   | l_303.edges  = (q_s2 -> q_x22) + (q_x22 -> q_x24) &&
	let l_304 = l_303.next   | l_304.edges  = (q_s2 -> q_x25) + (q_x25 -> q_x27) &&
	let l_305 = l_304.next   | l_305.edges  = (q_s2 -> q_x26) + (q_x26 -> q_x28) &&
	let l_306 = l_305.next   | l_306.edges  = (q_s2 -> q_x29) + (q_x29 -> q_x31) &&
	let l_307 = l_306.next   | l_307.edges  = (q_s2 -> q_x30) + (q_x30 -> q_x32) &&
	let l_308 = l_307.next   | l_308.edges  = (q_s2 -> q_x33) + (q_x33 -> q_x35) 
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
    lte[grph/last.numTele, 3696]
}

run finalLayer for 8 circGraph, 16 Int
