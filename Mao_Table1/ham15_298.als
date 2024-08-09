
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_x0, q_x1, q_x2, q_x3, q_x4, q_x5, q_x6, q_x7, q_x8, q_x9, q_x10, q_x11, q_x12, q_x13, q_x14, q_x15, q_x16, q_x17, q_x18, q_x19, q_x20, q_x21, q_x22, q_x23, q_x24, q_x25, q_x26, q_x27, q_x28, q_x29, q_x30, q_x31, q_x32, q_x33, q_x34, q_x35, q_x36, q_x37, q_x38, q_x39, q_x40, q_x41, q_x42, q_x43, q_x44 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3, M_4, M_5, M_6, M_7, M_8, M_9, M_10, M_11, M_12, M_13, M_14 extends Machine { }

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
	#(c.location).M_4 < 4 &&
	#(c.location).M_5 < 4 &&
	#(c.location).M_6 < 4 &&
	#(c.location).M_7 < 4 &&
	#(c.location).M_8 < 4 &&
	#(c.location).M_9 < 4 &&
	#(c.location).M_10 < 4 &&
	#(c.location).M_11 < 4 &&
	#(c.location).M_12 < 4 &&
	#(c.location).M_13 < 4 &&
	#(c.location).M_14 < 4
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
		(q_x13 -> M_4) + 
		(q_x14 -> M_4) + 
		(q_x15 -> M_5) + 
		(q_x16 -> M_5) + 
		(q_x17 -> M_5) + 
		(q_x18 -> M_6) + 
		(q_x19 -> M_6) + 
		(q_x20 -> M_6) + 
		(q_x21 -> M_7) + 
		(q_x22 -> M_7) + 
		(q_x23 -> M_7) + 
		(q_x24 -> M_8) + 
		(q_x25 -> M_8) + 
		(q_x26 -> M_8) + 
		(q_x27 -> M_9) + 
		(q_x28 -> M_9) + 
		(q_x29 -> M_9) + 
		(q_x30 -> M_10) + 
		(q_x31 -> M_10) + 
		(q_x32 -> M_10) + 
		(q_x33 -> M_11) + 
		(q_x34 -> M_11) + 
		(q_x35 -> M_11) + 
		(q_x36 -> M_12) + 
		(q_x37 -> M_12) + 
		(q_x38 -> M_12) + 
		(q_x39 -> M_13) + 
		(q_x40 -> M_13) + 
		(q_x41 -> M_13) + 
		(q_x42 -> M_14) + 
		(q_x43 -> M_14) + 
		(q_x44 -> M_14) &&
	let l_1 = l_0.next     | l_1.edges   = (q_x13 -> q_x15) &&
	let l_2 = l_1.next     | l_2.edges   = (q_x2 -> q_x15) +
                                               (q_x14 -> q_x16) &&
	let l_3 = l_2.next     | l_3.edges   = (q_x2 -> q_x16) &&
	let l_4 = l_3.next     | l_4.edges   = (q_x14 -> q_x15) + (q_x15 -> q_x16) &&
	let l_5 = l_4.next     | l_5.edges   = (q_x2 -> q_x14) + (q_x14 -> q_x16) +
                                               (q_x12 -> q_x17) &&
	let l_6 = l_5.next     | l_6.edges   = (q_x2 -> q_x17) &&
	let l_7 = l_6.next     | l_7.edges   = (q_x12 -> q_x16) + (q_x16 -> q_x17) &&
	let l_8 = l_7.next     | l_8.edges   = (q_x2 -> q_x12) + (q_x12 -> q_x17) +
                                               (q_x11 -> q_x18) &&
	let l_9 = l_8.next     | l_9.edges   = (q_x2 -> q_x18) &&
	let l_10 = l_9.next    | l_10.edges  = (q_x11 -> q_x17) + (q_x17 -> q_x18) &&
	let l_11 = l_10.next   | l_11.edges  = (q_x2 -> q_x11) + (q_x11 -> q_x18) &&
	let l_12 = l_11.next   | l_12.edges  = (q_x8 -> q_x18) &&
	let l_13 = l_12.next   | l_13.edges  = (q_x5 -> q_x18) &&
	let l_14 = l_13.next   | l_14.edges  = (q_x0 -> q_x18) &&
	let l_15 = l_14.next   | l_15.edges  = (q_x7 -> q_x18) &&
	let l_16 = l_15.next   | l_16.edges  = (q_x3 -> q_x18) &&
	let l_17 = l_16.next   | l_17.edges  = (q_x1 -> q_x18) +
                                               (q_x11 -> q_x19) &&
	let l_18 = l_17.next   | l_18.edges  = (q_x17 -> q_x19) &&
	let l_19 = l_18.next   | l_19.edges  = (q_x2 -> q_x11) + (q_x11 -> q_x19) &&
	let l_20 = l_19.next   | l_20.edges  = (q_x11 -> q_x17) + (q_x17 -> q_x19) &&
	let l_21 = l_20.next   | l_21.edges  = (q_x9 -> q_x19) &&
	let l_22 = l_21.next   | l_22.edges  = (q_x8 -> q_x19) &&
	let l_23 = l_22.next   | l_23.edges  = (q_x6 -> q_x19) &&
	let l_24 = l_23.next   | l_24.edges  = (q_x4 -> q_x19) &&
	let l_25 = l_24.next   | l_25.edges  = (q_x3 -> q_x19) &&
	let l_26 = l_25.next   | l_26.edges  = (q_x1 -> q_x19) +
                                               (q_x12 -> q_x20) &&
	let l_27 = l_26.next   | l_27.edges  = (q_x16 -> q_x20) &&
	let l_28 = l_27.next   | l_28.edges  = (q_x2 -> q_x12) + (q_x12 -> q_x20) &&
	let l_29 = l_28.next   | l_29.edges  = (q_x12 -> q_x16) + (q_x16 -> q_x20) +
                                               (q_x2 -> q_x21) &&
	let l_30 = l_29.next   | l_30.edges  = (q_x11 -> q_x20) + (q_x20 -> q_x21) &&
	let l_31 = l_30.next   | l_31.edges  = (q_x2 -> q_x11) + (q_x11 -> q_x21) &&
	let l_32 = l_31.next   | l_32.edges  = (q_x9 -> q_x21) &&
	let l_33 = l_32.next   | l_33.edges  = (q_x5 -> q_x21) &&
	let l_34 = l_33.next   | l_34.edges  = (q_x7 -> q_x21) &&
	let l_35 = l_34.next   | l_35.edges  = (q_x4 -> q_x21) &&
	let l_36 = l_35.next   | l_36.edges  = (q_x3 -> q_x21) &&
	let l_37 = l_36.next   | l_37.edges  = (q_x10 -> q_x21) +
                                               (q_x20 -> q_x22) &&
	let l_38 = l_37.next   | l_38.edges  = (q_x2 -> q_x11) + (q_x11 -> q_x22) &&
	let l_39 = l_38.next   | l_39.edges  = (q_x11 -> q_x20) + (q_x20 -> q_x22) &&
	let l_40 = l_39.next   | l_40.edges  = (q_x6 -> q_x22) &&
	let l_41 = l_40.next   | l_41.edges  = (q_x0 -> q_x22) &&
	let l_42 = l_41.next   | l_42.edges  = (q_x7 -> q_x22) &&
	let l_43 = l_42.next   | l_43.edges  = (q_x4 -> q_x22) &&
	let l_44 = l_43.next   | l_44.edges  = (q_x1 -> q_x22) &&
	let l_45 = l_44.next   | l_45.edges  = (q_x10 -> q_x22) +
                                               (q_x13 -> q_x14) + (q_x14 -> q_x23) &&
	let l_46 = l_45.next   | l_46.edges  = (q_x14 -> q_x23) &&
	let l_47 = l_46.next   | l_47.edges  = (q_x12 -> q_x23) + (q_x23 -> q_x24) &&
	let l_48 = l_47.next   | l_48.edges  = (q_x12 -> q_x24) &&
	let l_49 = l_48.next   | l_49.edges  = (q_x11 -> q_x24) + (q_x24 -> q_x25) &&
	let l_50 = l_49.next   | l_50.edges  = (q_x11 -> q_x25) &&
	let l_51 = l_50.next   | l_51.edges  = (q_x0 -> q_x25) +
                                               (q_x11 -> q_x26) &&
	let l_52 = l_51.next   | l_52.edges  = (q_x11 -> q_x24) + (q_x24 -> q_x26) &&
	let l_53 = l_52.next   | l_53.edges  = (q_x24 -> q_x26) &&
	let l_54 = l_53.next   | l_54.edges  = (q_x1 -> q_x26) +
                                               (q_x2 -> q_x27) &&
	let l_55 = l_54.next   | l_55.edges  = (q_x14 -> q_x15) + (q_x15 -> q_x27) &&
	let l_56 = l_55.next   | l_56.edges  = (q_x2 -> q_x14) + (q_x14 -> q_x27) &&
	let l_57 = l_56.next   | l_57.edges  = (q_x27 -> q_x28) &&
	let l_58 = l_57.next   | l_58.edges  = (q_x2 -> q_x12) + (q_x12 -> q_x28) &&
	let l_59 = l_58.next   | l_59.edges  = (q_x12 -> q_x27) + (q_x27 -> q_x28) +
                                               (q_x2 -> q_x29) &&
	let l_60 = l_59.next   | l_60.edges  = (q_x11 -> q_x28) + (q_x28 -> q_x29) &&
	let l_61 = l_60.next   | l_61.edges  = (q_x2 -> q_x11) + (q_x11 -> q_x29) +
                                               (q_x12 -> q_x30) &&
	let l_62 = l_61.next   | l_62.edges  = (q_x12 -> q_x23) + (q_x23 -> q_x30) &&
	let l_63 = l_62.next   | l_63.edges  = (q_x23 -> q_x30) +
                                               (q_x11 -> q_x31) &&
	let l_64 = l_63.next   | l_64.edges  = (q_x11 -> q_x30) + (q_x30 -> q_x31) &&
	let l_65 = l_64.next   | l_65.edges  = (q_x30 -> q_x31) &&
	let l_66 = l_65.next   | l_66.edges  = (q_x3 -> q_x31) +
                                               (q_x13 -> q_x14) + (q_x14 -> q_x32) &&
	let l_67 = l_66.next   | l_67.edges  = (q_x13 -> q_x32) &&
	let l_68 = l_67.next   | l_68.edges  = (q_x12 -> q_x32) + (q_x32 -> q_x33) &&
	let l_69 = l_68.next   | l_69.edges  = (q_x12 -> q_x33) &&
	let l_70 = l_69.next   | l_70.edges  = (q_x11 -> q_x33) + (q_x33 -> q_x34) &&
	let l_71 = l_70.next   | l_71.edges  = (q_x11 -> q_x34) &&
	let l_72 = l_71.next   | l_72.edges  = (q_x4 -> q_x34) +
                                               (q_x11 -> q_x35) &&
	let l_73 = l_72.next   | l_73.edges  = (q_x11 -> q_x33) + (q_x33 -> q_x35) &&
	let l_74 = l_73.next   | l_74.edges  = (q_x33 -> q_x35) &&
	let l_75 = l_74.next   | l_75.edges  = (q_x5 -> q_x35) +
                                               (q_x12 -> q_x36) &&
	let l_76 = l_75.next   | l_76.edges  = (q_x12 -> q_x32) + (q_x32 -> q_x36) &&
	let l_77 = l_76.next   | l_77.edges  = (q_x32 -> q_x36) &&
	let l_78 = l_77.next   | l_78.edges  = (q_x11 -> q_x36) + (q_x36 -> q_x37) &&
	let l_79 = l_78.next   | l_79.edges  = (q_x11 -> q_x37) &&
	let l_80 = l_79.next   | l_80.edges  = (q_x6 -> q_x37) +
                                               (q_x11 -> q_x38) &&
	let l_81 = l_80.next   | l_81.edges  = (q_x11 -> q_x36) + (q_x36 -> q_x38) &&
	let l_82 = l_81.next   | l_82.edges  = (q_x36 -> q_x38) &&
	let l_83 = l_82.next   | l_83.edges  = (q_x7 -> q_x38) +
                                               (q_x14 -> q_x39) &&
	let l_84 = l_83.next   | l_84.edges  = (q_x13 -> q_x14) + (q_x14 -> q_x39) &&
	let l_85 = l_84.next   | l_85.edges  = (q_x13 -> q_x39) &&
	let l_86 = l_85.next   | l_86.edges  = (q_x12 -> q_x39) + (q_x39 -> q_x40) &&
	let l_87 = l_86.next   | l_87.edges  = (q_x12 -> q_x40) &&
	let l_88 = l_87.next   | l_88.edges  = (q_x11 -> q_x40) + (q_x40 -> q_x41) &&
	let l_89 = l_88.next   | l_89.edges  = (q_x11 -> q_x41) &&
	let l_90 = l_89.next   | l_90.edges  = (q_x8 -> q_x41) +
                                               (q_x11 -> q_x42) &&
	let l_91 = l_90.next   | l_91.edges  = (q_x11 -> q_x40) + (q_x40 -> q_x42) &&
	let l_92 = l_91.next   | l_92.edges  = (q_x40 -> q_x42) &&
	let l_93 = l_92.next   | l_93.edges  = (q_x9 -> q_x42) +
                                               (q_x12 -> q_x43) &&
	let l_94 = l_93.next   | l_94.edges  = (q_x12 -> q_x39) + (q_x39 -> q_x43) &&
	let l_95 = l_94.next   | l_95.edges  = (q_x39 -> q_x43) &&
	let l_96 = l_95.next   | l_96.edges  = (q_x11 -> q_x43) + (q_x43 -> q_x44) &&
	let l_97 = l_96.next   | l_97.edges  = (q_x11 -> q_x44) &&
	let l_98 = l_97.next   | l_98.edges  = (q_x10 -> q_x44)
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
    lte[grph/last.numTele, 556]
}

run finalLayer for 99 circGraph, 14 Int
