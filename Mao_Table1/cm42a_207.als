
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_f9, q_f8, q_f7, q_f6, q_f5, q_f4, q_f3, q_f2, q_f1, q_f0, q_x3, q_x2, q_x1, q_x0 extends Qubit { }

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
		(q_f9 -> M_0) + 
		(q_f8 -> M_0) + 
		(q_f7 -> M_0) + 
		(q_f6 -> M_0) + 
		(q_f5 -> M_0) + 
		(q_f4 -> M_1) + 
		(q_f3 -> M_1) + 
		(q_f2 -> M_1) + 
		(q_f1 -> M_1) + 
		(q_f0 -> M_1) + 
		(q_x3 -> M_2) + 
		(q_x2 -> M_2) + 
		(q_x1 -> M_2) + 
		(q_x0 -> M_2) &&
	let l_1 = l_0.next   | l_1.edges  = (q_x3 -> q_f7) &&
	let l_2 = l_1.next   | l_2.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f2) &&
	let l_3 = l_2.next   | l_3.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f3) &&
	let l_4 = l_3.next   | l_4.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f6) &&
	let l_5 = l_4.next   | l_5.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f7) &&
	let l_6 = l_5.next   | l_6.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x3) + (q_x3 -> q_f2) &&
	let l_7 = l_6.next   | l_7.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x3) + (q_x3 -> q_f3) &&
	let l_8 = l_7.next   | l_8.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f4) &&
	let l_9 = l_8.next   | l_9.edges  = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f5) &&
	let l_10 = l_9.next  | l_10.edges = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f5) &&
	let l_11 = l_10.next | l_11.edges = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f7) &&
	let l_12 = l_11.next | l_12.edges = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f0) &&
	let l_13 = l_12.next | l_13.edges = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f1) &&
	let l_14 = l_13.next | l_14.edges = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f1) &&
	let l_15 = l_14.next | l_15.edges = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f3) &&
	let l_16 = l_15.next | l_16.edges = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f9) &&
	let l_17 = l_16.next | l_17.edges = (q_x0 -> q_x1) + (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f8) &&
	let l_18 = l_17.next | l_18.edges = (q_x1 -> q_x2) + (q_x2 -> q_x3) + (q_x3 -> q_f9) &&
	let l_19 = l_18.next | l_19.edges = (q_x2 -> q_x3) + (q_x3 -> q_f3) &&
	let l_20 = l_19.next | l_20.edges = (q_x2 -> q_x3) + (q_x3 -> q_f7)
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
    lte[grph/last.numTele, 36]
}

run finalLayer for 21 circGraph, 10 Int
