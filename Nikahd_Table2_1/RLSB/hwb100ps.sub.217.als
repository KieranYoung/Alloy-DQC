
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_x1, q_x2, q_x3, q_x4, q_x5, q_x6, q_x7, q_x8, q_x9, q_x10, q_x11, q_x12, q_x13, q_x14, q_x15, q_x16, q_x17, q_x18, q_x19, q_x20, q_x21, q_x22, q_x23, q_x24, q_x25, q_x26, q_x27, q_x28, q_x29, q_x30, q_x31, q_x32, q_x33, q_x34, q_x35, q_x36, q_x37, q_x38, q_x39, q_x40, q_x41, q_x42, q_x43, q_x44, q_x45, q_x46, q_x47, q_x48, q_x49, q_x50, q_x51, q_x52, q_x53, q_x54, q_x55, q_x56, q_x57, q_x58, q_x59, q_x60, q_x61, q_x62, q_x63, q_x64, q_x65, q_x66, q_x67, q_x68, q_x69, q_x70, q_x71, q_x72, q_x73, q_x74, q_x75, q_x76, q_x77, q_x78, q_x79, q_x80, q_x81, q_x82, q_x83, q_x84, q_x85, q_x86, q_x87, q_x88, q_x89, q_x90, q_x91, q_x92, q_x93, q_x94, q_x95, q_x96, q_x97, q_x98, q_x99, q_x100, q_s1, q_s2, q_s3, q_s4, q_s5, q_s6, q_s7 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3, M_4, M_5, M_6 extends Machine { }

sig circGraph{
    edges: Qubit -> Qubit,
    location: Qubit -> Machine,
    numTele: Int
} {
    all q: Qubit | #q.location = 1 
}

/*
fact { all c:circGraph |
	#(c.location).M_0 < 17 &&
	#(c.location).M_1 < 17 &&
	#(c.location).M_2 < 17 &&
	#(c.location).M_3 < 17 &&
	#(c.location).M_4 < 17 &&
	#(c.location).M_5 < 17 &&
	#(c.location).M_6 < 17
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 17 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_x1 -> M_5) + 
		(q_x2 -> M_6) + 
		(q_x3 -> M_5) + 
		(q_x4 -> M_5) + 
		(q_x5 -> M_5) + 
		(q_x6 -> M_5) + 
		(q_x7 -> M_1) + 
		(q_x8 -> M_3) + 
		(q_x9 -> M_3) + 
		(q_x10 -> M_3) + 
		(q_x11 -> M_3) + 
		(q_x12 -> M_4) + 
		(q_x13 -> M_4) + 
		(q_x14 -> M_6) + 
		(q_x15 -> M_4) + 
		(q_x16 -> M_4) + 
		(q_x17 -> M_6) + 
		(q_x18 -> M_6) + 
		(q_x19 -> M_6) + 
		(q_x20 -> M_6) + 
		(q_x21 -> M_1) + 
		(q_x22 -> M_3) + 
		(q_x23 -> M_1) + 
		(q_x24 -> M_4) + 
		(q_x25 -> M_0) + 
		(q_x26 -> M_6) + 
		(q_x27 -> M_0) + 
		(q_x28 -> M_6) + 
		(q_x29 -> M_0) + 
		(q_x30 -> M_1) + 
		(q_x31 -> M_0) + 
		(q_x32 -> M_5) + 
		(q_x33 -> M_5) + 
		(q_x34 -> M_5) + 
		(q_x35 -> M_5) + 
		(q_x36 -> M_2) + 
		(q_x37 -> M_1) + 
		(q_x38 -> M_1) + 
		(q_x39 -> M_1) + 
		(q_x40 -> M_3) + 
		(q_x41 -> M_3) + 
		(q_x42 -> M_4) + 
		(q_x43 -> M_3) + 
		(q_x44 -> M_1) + 
		(q_x45 -> M_4) + 
		(q_x46 -> M_0) + 
		(q_x47 -> M_4) + 
		(q_x48 -> M_4) + 
		(q_x49 -> M_0) + 
		(q_x50 -> M_0) + 
		(q_x51 -> M_0) + 
		(q_x52 -> M_0) + 
		(q_x53 -> M_1) + 
		(q_x54 -> M_5) + 
		(q_x55 -> M_1) + 
		(q_x56 -> M_3) + 
		(q_x57 -> M_6) + 
		(q_x58 -> M_6) + 
		(q_x59 -> M_6) + 
		(q_x60 -> M_1) + 
		(q_x61 -> M_1) + 
		(q_x62 -> M_1) + 
		(q_x63 -> M_1) + 
		(q_x64 -> M_5) + 
		(q_x65 -> M_0) + 
		(q_x66 -> M_3) + 
		(q_x67 -> M_0) + 
		(q_x68 -> M_0) + 
		(q_x69 -> M_4) + 
		(q_x70 -> M_1) + 
		(q_x71 -> M_4) + 
		(q_x72 -> M_4) + 
		(q_x73 -> M_4) + 
		(q_x74 -> M_4) + 
		(q_x75 -> M_4) + 
		(q_x76 -> M_5) + 
		(q_x77 -> M_3) + 
		(q_x78 -> M_3) + 
		(q_x79 -> M_3) + 
		(q_x80 -> M_3) + 
		(q_x81 -> M_5) + 
		(q_x82 -> M_0) + 
		(q_x83 -> M_5) + 
		(q_x84 -> M_5) + 
		(q_x85 -> M_6) + 
		(q_x86 -> M_6) + 
		(q_x87 -> M_1) + 
		(q_x88 -> M_2) + 
		(q_x89 -> M_2) + 
		(q_x90 -> M_2) + 
		(q_x91 -> M_2) + 
		(q_x92 -> M_3) + 
		(q_x93 -> M_2) + 
		(q_x94 -> M_2) + 
		(q_x95 -> M_2) + 
		(q_x96 -> M_2) + 
		(q_x97 -> M_2) + 
		(q_x98 -> M_2) + 
		(q_x99 -> M_6) + 
		(q_x100 -> M_6) + 
		(q_s1 -> M_5) + 
		(q_s2 -> M_2) + 
		(q_s3 -> M_2) + 
		(q_s4 -> M_2) + 
		(q_s5 -> M_2) + 
		(q_s6 -> M_0) + 
		(q_s7 -> M_2) &&

	let l_652 = l_0.next   | l_652.edges  = (q_s1 -> q_x85) + (q_x85 -> q_x87) &&
	let l_653 = l_652.next   | l_653.edges  = (q_s1 -> q_x89) + (q_x89 -> q_x91) &&
	let l_654 = l_653.next   | l_654.edges  = (q_s1 -> q_x93) + (q_x93 -> q_x95) 
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
    lte[grph/last.numTele, 16745]
}

run finalLayer for 4 circGraph, 19 Int
