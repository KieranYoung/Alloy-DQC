
module teleport

open util/ordering[circGraph] as grph
open util/integer

abstract sig Qubit { }
one sig q_a, q_b, q_c, q_d, q_e, q_f, q_g, q_h, q_i, q_j, q_k, q_l, q_m, q_n, q_o extends Qubit { }

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
		(q_a -> M_0) + 
		(q_b -> M_0) + 
		(q_c -> M_0) + 
		(q_d -> M_0) + 
		(q_e -> M_0) + 
		(q_f -> M_0) + 
		(q_g -> M_0) + 
		(q_h -> M_0) + 
		(q_i -> M_1) + 
		(q_j -> M_1) + 
		(q_k -> M_1) + 
		(q_l -> M_1) + 
		(q_m -> M_1) + 
		(q_n -> M_1) + 
		(q_o -> M_1) &&
	let l_1 = l_0.next     | l_1.edges   = (q_f -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_2 = l_1.next     | l_2.edges   = (q_f -> q_j) + (q_j -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_3 = l_2.next     | l_3.edges   = (q_j -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_4 = l_3.next     | l_4.edges   = (q_j -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_5 = l_4.next     | l_5.edges   = (q_c -> q_j) + (q_j -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_6 = l_5.next     | l_6.edges   = (q_c -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_7 = l_6.next     | l_7.edges   = (q_c -> q_f) + (q_f -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_8 = l_7.next     | l_8.edges   = (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_c) &&
	let l_9 = l_8.next     | l_9.edges   = (q_f -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_c) &&
	let l_10 = l_9.next    | l_10.edges  = (q_c -> q_j) + (q_j -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_11 = l_10.next   | l_11.edges  = (q_c -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_12 = l_11.next   | l_12.edges  = (q_c -> q_f) + (q_f -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_13 = l_12.next   | l_13.edges  = (q_h -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_14 = l_13.next   | l_14.edges  = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_h) &&
	let l_15 = l_14.next   | l_15.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_h) &&
	let l_16 = l_15.next   | l_16.edges  = (q_h -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_17 = l_16.next   | l_17.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_d) &&
	let l_18 = l_17.next   | l_18.edges  = (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_d) &&
	let l_19 = l_18.next   | l_19.edges  = (q_f -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_d) &&
	let l_20 = l_19.next   | l_20.edges  = (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_m) &&
	let l_21 = l_20.next   | l_21.edges  = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_22 = l_21.next   | l_22.edges  = (q_f -> q_j) + (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_23 = l_22.next   | l_23.edges  = (q_f -> q_k) + (q_k -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_24 = l_23.next   | l_24.edges  = (q_k -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_25 = l_24.next   | l_25.edges  = (q_j -> q_k) + (q_k -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_26 = l_25.next   | l_26.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_j) &&
	let l_27 = l_26.next   | l_27.edges  = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_k) &&
	let l_28 = l_27.next   | l_28.edges  = (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_c) &&
	let l_29 = l_28.next   | l_29.edges  = (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_n) &&
	let l_30 = l_29.next   | l_30.edges  = (q_f -> q_k) + (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_c) &&
	let l_31 = l_30.next   | l_31.edges  = (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_c) &&
	let l_32 = l_31.next   | l_32.edges  = (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_d) &&
	let l_33 = l_32.next   | l_33.edges  = (q_c -> q_j) + (q_j -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_34 = l_33.next   | l_34.edges  = (q_j -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_35 = l_34.next   | l_35.edges  = (q_j -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_36 = l_35.next   | l_36.edges  = (q_f -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_k) &&
	let l_37 = l_36.next   | l_37.edges  = (q_c -> q_f) + (q_f -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_38 = l_37.next   | l_38.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_f) &&
	let l_39 = l_38.next   | l_39.edges  = (q_f -> q_l) + (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_c) &&
	let l_40 = l_39.next   | l_40.edges  = (q_c -> q_f) + (q_f -> q_j) + (q_j -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_41 = l_40.next   | l_41.edges  = (q_f -> q_j) + (q_j -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_42 = l_41.next   | l_42.edges  = (q_c -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_43 = l_42.next   | l_43.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_a) &&
	let l_44 = l_43.next   | l_44.edges  = (q_f -> q_m) + (q_m -> q_o) + (q_o -> q_n) &&
	let l_45 = l_44.next   | l_45.edges  = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_l) &&
	let l_46 = l_45.next   | l_46.edges  = (q_f -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_47 = l_46.next   | l_47.edges  = (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_k) &&
	let l_48 = l_47.next   | l_48.edges  = (q_c -> q_j) + (q_j -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_49 = l_48.next   | l_49.edges  = (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_c) &&
	let l_50 = l_49.next   | l_50.edges  = (q_f -> q_m) + (q_m -> q_o) + (q_o -> q_j) &&
	let l_51 = l_50.next   | l_51.edges  = (q_n -> q_o) + (q_o -> q_m) &&
	let l_52 = l_51.next   | l_52.edges  = (q_m -> q_o) + (q_o -> q_n) &&
	let l_53 = l_52.next   | l_53.edges  = (q_c -> q_m) + (q_m -> q_o) + (q_o -> q_b) &&
	let l_54 = l_53.next   | l_54.edges  = (q_m -> q_o) + (q_o -> q_c) &&
	let l_55 = l_54.next   | l_55.edges  = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_j) &&
	let l_56 = l_55.next   | l_56.edges  = (q_c -> q_j) + (q_j -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_b) &&
	let l_57 = l_56.next   | l_57.edges  = (q_c -> q_l) + (q_l -> q_o) + (q_o -> q_m) &&
	let l_58 = l_57.next   | l_58.edges  = (q_c -> q_k) + (q_k -> q_l) + (q_l -> q_o) + (q_o -> q_m) &&
	let l_59 = l_58.next   | l_59.edges  = (q_k -> q_l) + (q_l -> q_o) + (q_o -> q_m) &&
	let l_60 = l_59.next   | l_60.edges  = (q_m -> q_o) + (q_o -> q_l) &&
	let l_61 = l_60.next   | l_61.edges  = (q_m -> q_o) + (q_o -> q_c) &&
	let l_62 = l_61.next   | l_62.edges  = (q_l -> q_o) + (q_o -> q_m) &&
	let l_63 = l_62.next   | l_63.edges  = (q_m -> q_o) + (q_o -> q_k) &&
	let l_64 = l_63.next   | l_64.edges  = (q_k -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_c) &&
	let l_65 = l_64.next   | l_65.edges  = (q_c -> q_k) + (q_k -> q_m) + (q_m -> q_o) + (q_o -> q_l) &&
	let l_66 = l_65.next   | l_66.edges  = (q_f -> q_o) + (q_o -> q_l) &&
	let l_67 = l_66.next   | l_67.edges  = (q_f -> q_o) + (q_o -> q_m) &&
	let l_68 = l_67.next   | l_68.edges  = (q_f -> q_l) + (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_d) &&
	let l_69 = l_68.next   | l_69.edges  = (q_o -> q_m) &&
	let l_70 = l_69.next   | l_70.edges  = (q_m -> q_o) + (q_o -> q_l) &&
	let l_71 = l_70.next   | l_71.edges  = (q_l -> q_m) + (q_m -> q_o) + (q_o -> q_d) &&
	let l_72 = l_71.next   | l_72.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) &&
	let l_73 = l_72.next   | l_73.edges  = (q_n -> q_o) + (q_o -> q_f) &&
	let l_74 = l_73.next   | l_74.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_e) &&
	let l_75 = l_74.next   | l_75.edges  = (q_f -> q_m) + (q_m -> q_n) + (q_n -> q_o) &&
	let l_76 = l_75.next   | l_76.edges  = (q_o -> q_m) &&
	let l_77 = l_76.next   | l_77.edges  = (q_n -> q_o) + (q_o -> q_f) &&
	let l_78 = l_77.next   | l_78.edges  = (q_m -> q_n) + (q_n -> q_o) &&
	let l_79 = l_78.next   | l_79.edges  = (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_f) &&
	let l_80 = l_79.next   | l_80.edges  = (q_f -> q_o) + (q_o -> q_m) &&
	let l_81 = l_80.next   | l_81.edges  = (q_o -> q_n) &&
	let l_82 = l_81.next   | l_82.edges  = (q_l -> q_n) + (q_n -> q_o) &&
	let l_83 = l_82.next   | l_83.edges  = (q_l -> q_n) + (q_n -> q_k) &&
	let l_84 = l_83.next   | l_84.edges  = (q_l -> q_n) + (q_n -> q_m) &&
	let l_85 = l_84.next   | l_85.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_j) &&
	let l_86 = l_85.next   | l_86.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_g) &&
	let l_87 = l_86.next   | l_87.edges  = (q_m -> q_o) + (q_o -> q_n) &&
	let l_88 = l_87.next   | l_88.edges  = (q_m -> q_o) + (q_o -> q_l) &&
	let l_89 = l_88.next   | l_89.edges  = (q_n -> q_o) &&
	let l_90 = l_89.next   | l_90.edges  = (q_o -> q_l) &&
	let l_91 = l_90.next   | l_91.edges  = (q_l -> q_n) + (q_n -> q_o) + (q_o -> q_h) &&
	let l_92 = l_91.next   | l_92.edges  = (q_l -> q_m) + (q_m -> q_o) &&
	let l_93 = l_92.next   | l_93.edges  = (q_o -> q_n) &&
	let l_94 = l_93.next   | l_94.edges  = (q_l -> q_m) + (q_m -> q_n) + (q_n -> q_o) + (q_o -> q_i) &&
	let l_95 = l_94.next   | l_95.edges  = (q_l -> q_o) &&
	let l_96 = l_95.next   | l_96.edges  = (q_o -> q_l) +
                                               (q_m -> q_n) &&
	let l_97 = l_96.next   | l_97.edges  = (q_k -> q_o) +
                                               (q_m -> q_n) + (q_n -> q_j) &&
	let l_98 = l_97.next   | l_98.edges  = (q_n -> q_m) &&
	let l_99 = l_98.next   | l_99.edges  = (q_k -> q_n) &&
	let l_100 = l_99.next  | l_100.edges = (q_n -> q_j) &&
	let l_101 = l_100.next | l_101.edges = (q_j -> q_n) &&
	let l_102 = l_101.next | l_102.edges = (q_j -> q_m) &&
	let l_103 = l_102.next | l_103.edges = (q_m -> q_i) &&
	let l_104 = l_103.next | l_104.edges = (q_i -> q_m) &&
	let l_105 = l_104.next | l_105.edges = (q_m -> q_l) &&
	let l_106 = l_105.next | l_106.edges = (q_j -> q_l) &&
	let l_107 = l_106.next | l_107.edges = (q_l -> q_h) &&
	let l_108 = l_107.next | l_108.edges = (q_h -> q_l) &&
	let l_109 = l_108.next | l_109.edges = (q_h -> q_k) &&
	let l_110 = l_109.next | l_110.edges = (q_k -> q_g) &&
	let l_111 = l_110.next | l_111.edges = (q_g -> q_k) &&
	let l_112 = l_111.next | l_112.edges = (q_g -> q_j) &&
	let l_113 = l_112.next | l_113.edges = (q_j -> q_f) &&
	let l_114 = l_113.next | l_114.edges = (q_f -> q_j) &&
	let l_115 = l_114.next | l_115.edges = (q_f -> q_i) &&
	let l_116 = l_115.next | l_116.edges = (q_i -> q_e) &&
	let l_117 = l_116.next | l_117.edges = (q_e -> q_i) &&
	let l_118 = l_117.next | l_118.edges = (q_e -> q_h) &&
	let l_119 = l_118.next | l_119.edges = (q_h -> q_d) &&
	let l_120 = l_119.next | l_120.edges = (q_d -> q_h) &&
	let l_121 = l_120.next | l_121.edges = (q_d -> q_g) &&
	let l_122 = l_121.next | l_122.edges = (q_g -> q_c) &&
	let l_123 = l_122.next | l_123.edges = (q_c -> q_g) &&
	let l_124 = l_123.next | l_124.edges = (q_c -> q_f) &&
	let l_125 = l_124.next | l_125.edges = (q_f -> q_b) &&
	let l_126 = l_125.next | l_126.edges = (q_b -> q_f) &&
	let l_127 = l_126.next | l_127.edges = (q_b -> q_e) &&
	let l_128 = l_127.next | l_128.edges = (q_e -> q_a) &&
	let l_129 = l_128.next | l_129.edges = (q_a -> q_e) &&
	let l_130 = l_129.next | l_130.edges = (q_a -> q_d)
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
    lte[grph/last.numTele, 245]
}

run finalLayer for 131 circGraph, 12 Int
