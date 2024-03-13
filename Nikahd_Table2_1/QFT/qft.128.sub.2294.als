
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_0, q_1, q_2, q_3, q_4, q_5, q_6, q_7, q_8, q_9, q_10, q_11, q_12, q_13, q_14, q_15, q_16, q_17, q_18, q_19, q_20, q_21, q_22, q_23, q_24, q_25, q_26, q_27, q_28, q_29, q_30, q_31, q_32, q_33, q_34, q_35, q_36, q_37, q_38, q_39, q_40, q_41, q_42, q_43, q_44, q_45, q_46, q_47, q_48, q_49, q_50, q_51, q_52, q_53, q_54, q_55, q_56, q_57, q_58, q_59, q_60, q_61, q_62, q_63, q_64, q_65, q_66, q_67, q_68, q_69, q_70, q_71, q_72, q_73, q_74, q_75, q_76, q_77, q_78, q_79, q_80, q_81, q_82, q_83, q_84, q_85, q_86, q_87, q_88, q_89, q_90, q_91, q_92, q_93, q_94, q_95, q_96, q_97, q_98, q_99, q_100, q_101, q_102, q_103, q_104, q_105, q_106, q_107, q_108, q_109, q_110, q_111, q_112, q_113, q_114, q_115, q_116, q_117, q_118, q_119, q_120, q_121, q_122, q_123, q_124, q_125, q_126, q_127 extends Qubit { }

abstract sig Machine { } 
one sig M_0, M_1, M_2, M_3, M_4, M_5, M_6, M_7 extends Machine { }

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
	#(c.location).M_6 < 17 &&
	#(c.location).M_7 < 17
}
*/
fact { all c:circGraph, m:Machine | #(c.location).m < 17 }

fact CircuitGraph {
    let l_0 = grph/first | 
        l_0.numTele = 0 &&
        l_0.location =
		(q_0 -> M_0) + 
		(q_1 -> M_6) + 
		(q_2 -> M_5) + 
		(q_3 -> M_5) + 
		(q_4 -> M_2) + 
		(q_5 -> M_5) + 
		(q_6 -> M_6) + 
		(q_7 -> M_5) + 
		(q_8 -> M_1) + 
		(q_9 -> M_2) + 
		(q_10 -> M_1) + 
		(q_11 -> M_4) + 
		(q_12 -> M_5) + 
		(q_13 -> M_5) + 
		(q_14 -> M_2) + 
		(q_15 -> M_6) + 
		(q_16 -> M_5) + 
		(q_17 -> M_0) + 
		(q_18 -> M_5) + 
		(q_19 -> M_5) + 
		(q_20 -> M_5) + 
		(q_21 -> M_0) + 
		(q_22 -> M_6) + 
		(q_23 -> M_3) + 
		(q_24 -> M_6) + 
		(q_25 -> M_2) + 
		(q_26 -> M_6) + 
		(q_27 -> M_5) + 
		(q_28 -> M_2) + 
		(q_29 -> M_5) + 
		(q_30 -> M_0) + 
		(q_31 -> M_0) + 
		(q_32 -> M_3) + 
		(q_33 -> M_3) + 
		(q_34 -> M_4) + 
		(q_35 -> M_5) + 
		(q_36 -> M_5) + 
		(q_37 -> M_6) + 
		(q_38 -> M_4) + 
		(q_39 -> M_1) + 
		(q_40 -> M_6) + 
		(q_41 -> M_6) + 
		(q_42 -> M_6) + 
		(q_43 -> M_6) + 
		(q_44 -> M_6) + 
		(q_45 -> M_5) + 
		(q_46 -> M_3) + 
		(q_47 -> M_5) + 
		(q_48 -> M_6) + 
		(q_49 -> M_7) + 
		(q_50 -> M_7) + 
		(q_51 -> M_7) + 
		(q_52 -> M_4) + 
		(q_53 -> M_1) + 
		(q_54 -> M_6) + 
		(q_55 -> M_2) + 
		(q_56 -> M_7) + 
		(q_57 -> M_7) + 
		(q_58 -> M_0) + 
		(q_59 -> M_6) + 
		(q_60 -> M_7) + 
		(q_61 -> M_7) + 
		(q_62 -> M_7) + 
		(q_63 -> M_4) + 
		(q_64 -> M_7) + 
		(q_65 -> M_4) + 
		(q_66 -> M_0) + 
		(q_67 -> M_6) + 
		(q_68 -> M_0) + 
		(q_69 -> M_7) + 
		(q_70 -> M_7) + 
		(q_71 -> M_0) + 
		(q_72 -> M_3) + 
		(q_73 -> M_1) + 
		(q_74 -> M_1) + 
		(q_75 -> M_7) + 
		(q_76 -> M_1) + 
		(q_77 -> M_1) + 
		(q_78 -> M_1) + 
		(q_79 -> M_2) + 
		(q_80 -> M_2) + 
		(q_81 -> M_2) + 
		(q_82 -> M_2) + 
		(q_83 -> M_2) + 
		(q_84 -> M_2) + 
		(q_85 -> M_2) + 
		(q_86 -> M_2) + 
		(q_87 -> M_2) + 
		(q_88 -> M_2) + 
		(q_89 -> M_0) + 
		(q_90 -> M_0) + 
		(q_91 -> M_0) + 
		(q_92 -> M_0) + 
		(q_93 -> M_0) + 
		(q_94 -> M_0) + 
		(q_95 -> M_3) + 
		(q_96 -> M_3) + 
		(q_97 -> M_4) + 
		(q_98 -> M_4) + 
		(q_99 -> M_4) + 
		(q_100 -> M_4) + 
		(q_101 -> M_4) + 
		(q_102 -> M_4) + 
		(q_103 -> M_4) + 
		(q_104 -> M_4) + 
		(q_105 -> M_4) + 
		(q_106 -> M_4) + 
		(q_107 -> M_3) + 
		(q_108 -> M_3) + 
		(q_109 -> M_3) + 
		(q_110 -> M_3) + 
		(q_111 -> M_3) + 
		(q_112 -> M_3) + 
		(q_113 -> M_3) + 
		(q_114 -> M_3) + 
		(q_115 -> M_3) + 
		(q_116 -> M_1) + 
		(q_117 -> M_7) + 
		(q_118 -> M_1) + 
		(q_119 -> M_1) + 
		(q_120 -> M_1) + 
		(q_121 -> M_0) + 
		(q_122 -> M_7) + 
		(q_123 -> M_7) + 
		(q_124 -> M_7) + 
		(q_125 -> M_1) + 
		(q_126 -> M_1) + 
		(q_127 -> M_1) &&

	let l_6883 = l_0.next | l_6883.edges = (q_79 -> q_89) &&
	let l_6884 = l_6883.next | l_6884.edges = (q_79 -> q_90) &&
	let l_6885 = l_6884.next | l_6885.edges = (q_79 -> q_91) 
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
    lte[grph/last.numTele, 128064]
}

run finalLayer for 4 circGraph, 21 Int
