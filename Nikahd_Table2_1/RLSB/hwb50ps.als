
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
		(q_x1 -> M_0) + 
		(q_x2 -> M_3) + 
		(q_x3 -> M_2) + 
		(q_x4 -> M_0) + 
		(q_x5 -> M_1) + 
		(q_x6 -> M_4) + 
		(q_x7 -> M_2) + 
		(q_x8 -> M_2) + 
		(q_x9 -> M_3) + 
		(q_x10 -> M_3) + 
		(q_x11 -> M_1) + 
		(q_x12 -> M_0) + 
		(q_x13 -> M_1) + 
		(q_x14 -> M_0) + 
		(q_x15 -> M_2) + 
		(q_x16 -> M_4) + 
		(q_x17 -> M_4) + 
		(q_x18 -> M_2) + 
		(q_x19 -> M_0) + 
		(q_x20 -> M_0) + 
		(q_x21 -> M_3) + 
		(q_x22 -> M_1) + 
		(q_x23 -> M_1) + 
		(q_x24 -> M_1) + 
		(q_x25 -> M_3) + 
		(q_x26 -> M_3) + 
		(q_x27 -> M_4) + 
		(q_x28 -> M_2) + 
		(q_x29 -> M_0) + 
		(q_x30 -> M_0) + 
		(q_x31 -> M_3) + 
		(q_x32 -> M_1) + 
		(q_x33 -> M_1) + 
		(q_x34 -> M_2) + 
		(q_x35 -> M_4) + 
		(q_x36 -> M_4) + 
		(q_x37 -> M_1) + 
		(q_x38 -> M_3) + 
		(q_x39 -> M_0) + 
		(q_x40 -> M_2) + 
		(q_x41 -> M_2) + 
		(q_x42 -> M_2) + 
		(q_x43 -> M_4) + 
		(q_x44 -> M_1) + 
		(q_x45 -> M_1) + 
		(q_x46 -> M_2) + 
		(q_x47 -> M_4) + 
		(q_x48 -> M_4) + 
		(q_x49 -> M_4) + 
		(q_x50 -> M_3) + 
		(q_s1 -> M_4) + 
		(q_s2 -> M_0) + 
		(q_s3 -> M_3) + 
		(q_s4 -> M_1) + 
		(q_s5 -> M_4) + 
		(q_s6 -> M_0) &&
	let l_1 = l_0.next       | l_1.edges    = (q_x1 -> q_s1) &&
	let l_2 = l_1.next       | l_2.edges    = (q_x2 -> q_s1) + (q_s1 -> q_s2) &&
	let l_3 = l_2.next       | l_3.edges    = (q_x2 -> q_s1) &&
	let l_4 = l_3.next       | l_4.edges    = (q_x3 -> q_s1) + (q_s1 -> q_s2) &&
	let l_5 = l_4.next       | l_5.edges    = (q_x3 -> q_s1) &&
	let l_6 = l_5.next       | l_6.edges    = (q_x4 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_7 = l_6.next       | l_7.edges    = (q_x4 -> q_s1) + (q_s1 -> q_s2) &&
	let l_8 = l_7.next       | l_8.edges    = (q_x4 -> q_s1) &&
	let l_9 = l_8.next       | l_9.edges    = (q_x5 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_10 = l_9.next      | l_10.edges   = (q_x5 -> q_s1) + (q_s1 -> q_s2) &&
	let l_11 = l_10.next     | l_11.edges   = (q_x5 -> q_s1) &&
	let l_12 = l_11.next     | l_12.edges   = (q_x6 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_13 = l_12.next     | l_13.edges   = (q_x6 -> q_s1) + (q_s1 -> q_s2) &&
	let l_14 = l_13.next     | l_14.edges   = (q_x6 -> q_s1) &&
	let l_15 = l_14.next     | l_15.edges   = (q_x7 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_16 = l_15.next     | l_16.edges   = (q_x7 -> q_s1) + (q_s1 -> q_s2) &&
	let l_17 = l_16.next     | l_17.edges   = (q_x7 -> q_s1) &&
	let l_18 = l_17.next     | l_18.edges   = (q_x8 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_19 = l_18.next     | l_19.edges   = (q_x8 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_20 = l_19.next     | l_20.edges   = (q_x8 -> q_s1) + (q_s1 -> q_s2) &&
	let l_21 = l_20.next     | l_21.edges   = (q_x8 -> q_s1) &&
	let l_22 = l_21.next     | l_22.edges   = (q_x9 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_23 = l_22.next     | l_23.edges   = (q_x9 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_24 = l_23.next     | l_24.edges   = (q_x9 -> q_s1) + (q_s1 -> q_s2) &&
	let l_25 = l_24.next     | l_25.edges   = (q_x9 -> q_s1) &&
	let l_26 = l_25.next     | l_26.edges   = (q_x10 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_27 = l_26.next     | l_27.edges   = (q_x10 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_28 = l_27.next     | l_28.edges   = (q_x10 -> q_s1) + (q_s1 -> q_s2) &&
	let l_29 = l_28.next     | l_29.edges   = (q_x10 -> q_s1) &&
	let l_30 = l_29.next     | l_30.edges   = (q_x11 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_31 = l_30.next     | l_31.edges   = (q_x11 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_32 = l_31.next     | l_32.edges   = (q_x11 -> q_s1) + (q_s1 -> q_s2) &&
	let l_33 = l_32.next     | l_33.edges   = (q_x11 -> q_s1) &&
	let l_34 = l_33.next     | l_34.edges   = (q_x12 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_35 = l_34.next     | l_35.edges   = (q_x12 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_36 = l_35.next     | l_36.edges   = (q_x12 -> q_s1) + (q_s1 -> q_s2) &&
	let l_37 = l_36.next     | l_37.edges   = (q_x12 -> q_s1) &&
	let l_38 = l_37.next     | l_38.edges   = (q_x13 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_39 = l_38.next     | l_39.edges   = (q_x13 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_40 = l_39.next     | l_40.edges   = (q_x13 -> q_s1) + (q_s1 -> q_s2) &&
	let l_41 = l_40.next     | l_41.edges   = (q_x13 -> q_s1) &&
	let l_42 = l_41.next     | l_42.edges   = (q_x14 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_43 = l_42.next     | l_43.edges   = (q_x14 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_44 = l_43.next     | l_44.edges   = (q_x14 -> q_s1) + (q_s1 -> q_s2) &&
	let l_45 = l_44.next     | l_45.edges   = (q_x14 -> q_s1) &&
	let l_46 = l_45.next     | l_46.edges   = (q_x15 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_47 = l_46.next     | l_47.edges   = (q_x15 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_48 = l_47.next     | l_48.edges   = (q_x15 -> q_s1) + (q_s1 -> q_s2) &&
	let l_49 = l_48.next     | l_49.edges   = (q_x15 -> q_s1) &&
	let l_50 = l_49.next     | l_50.edges   = (q_x16 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_51 = l_50.next     | l_51.edges   = (q_x16 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_52 = l_51.next     | l_52.edges   = (q_x16 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_53 = l_52.next     | l_53.edges   = (q_x16 -> q_s1) + (q_s1 -> q_s2) &&
	let l_54 = l_53.next     | l_54.edges   = (q_x16 -> q_s1) &&
	let l_55 = l_54.next     | l_55.edges   = (q_x17 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_56 = l_55.next     | l_56.edges   = (q_x17 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_57 = l_56.next     | l_57.edges   = (q_x17 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_58 = l_57.next     | l_58.edges   = (q_x17 -> q_s1) + (q_s1 -> q_s2) &&
	let l_59 = l_58.next     | l_59.edges   = (q_x17 -> q_s1) &&
	let l_60 = l_59.next     | l_60.edges   = (q_x18 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_61 = l_60.next     | l_61.edges   = (q_x18 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_62 = l_61.next     | l_62.edges   = (q_x18 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_63 = l_62.next     | l_63.edges   = (q_x18 -> q_s1) + (q_s1 -> q_s2) &&
	let l_64 = l_63.next     | l_64.edges   = (q_x18 -> q_s1) &&
	let l_65 = l_64.next     | l_65.edges   = (q_x19 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_66 = l_65.next     | l_66.edges   = (q_x19 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_67 = l_66.next     | l_67.edges   = (q_x19 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_68 = l_67.next     | l_68.edges   = (q_x19 -> q_s1) + (q_s1 -> q_s2) &&
	let l_69 = l_68.next     | l_69.edges   = (q_x19 -> q_s1) &&
	let l_70 = l_69.next     | l_70.edges   = (q_x20 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_71 = l_70.next     | l_71.edges   = (q_x20 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_72 = l_71.next     | l_72.edges   = (q_x20 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_73 = l_72.next     | l_73.edges   = (q_x20 -> q_s1) + (q_s1 -> q_s2) &&
	let l_74 = l_73.next     | l_74.edges   = (q_x20 -> q_s1) &&
	let l_75 = l_74.next     | l_75.edges   = (q_x21 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_76 = l_75.next     | l_76.edges   = (q_x21 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_77 = l_76.next     | l_77.edges   = (q_x21 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_78 = l_77.next     | l_78.edges   = (q_x21 -> q_s1) + (q_s1 -> q_s2) &&
	let l_79 = l_78.next     | l_79.edges   = (q_x21 -> q_s1) &&
	let l_80 = l_79.next     | l_80.edges   = (q_x22 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_81 = l_80.next     | l_81.edges   = (q_x22 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_82 = l_81.next     | l_82.edges   = (q_x22 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_83 = l_82.next     | l_83.edges   = (q_x22 -> q_s1) + (q_s1 -> q_s2) &&
	let l_84 = l_83.next     | l_84.edges   = (q_x22 -> q_s1) &&
	let l_85 = l_84.next     | l_85.edges   = (q_x23 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_86 = l_85.next     | l_86.edges   = (q_x23 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_87 = l_86.next     | l_87.edges   = (q_x23 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_88 = l_87.next     | l_88.edges   = (q_x23 -> q_s1) + (q_s1 -> q_s2) &&
	let l_89 = l_88.next     | l_89.edges   = (q_x23 -> q_s1) &&
	let l_90 = l_89.next     | l_90.edges   = (q_x24 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_91 = l_90.next     | l_91.edges   = (q_x24 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_92 = l_91.next     | l_92.edges   = (q_x24 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_93 = l_92.next     | l_93.edges   = (q_x24 -> q_s1) + (q_s1 -> q_s2) &&
	let l_94 = l_93.next     | l_94.edges   = (q_x24 -> q_s1) &&
	let l_95 = l_94.next     | l_95.edges   = (q_x25 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_96 = l_95.next     | l_96.edges   = (q_x25 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_97 = l_96.next     | l_97.edges   = (q_x25 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_98 = l_97.next     | l_98.edges   = (q_x25 -> q_s1) + (q_s1 -> q_s2) &&
	let l_99 = l_98.next     | l_99.edges   = (q_x25 -> q_s1) &&
	let l_100 = l_99.next    | l_100.edges  = (q_x26 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_101 = l_100.next   | l_101.edges  = (q_x26 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_102 = l_101.next   | l_102.edges  = (q_x26 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_103 = l_102.next   | l_103.edges  = (q_x26 -> q_s1) + (q_s1 -> q_s2) &&
	let l_104 = l_103.next   | l_104.edges  = (q_x26 -> q_s1) &&
	let l_105 = l_104.next   | l_105.edges  = (q_x27 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_106 = l_105.next   | l_106.edges  = (q_x27 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_107 = l_106.next   | l_107.edges  = (q_x27 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_108 = l_107.next   | l_108.edges  = (q_x27 -> q_s1) + (q_s1 -> q_s2) &&
	let l_109 = l_108.next   | l_109.edges  = (q_x27 -> q_s1) &&
	let l_110 = l_109.next   | l_110.edges  = (q_x28 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_111 = l_110.next   | l_111.edges  = (q_x28 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_112 = l_111.next   | l_112.edges  = (q_x28 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_113 = l_112.next   | l_113.edges  = (q_x28 -> q_s1) + (q_s1 -> q_s2) &&
	let l_114 = l_113.next   | l_114.edges  = (q_x28 -> q_s1) &&
	let l_115 = l_114.next   | l_115.edges  = (q_x29 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_116 = l_115.next   | l_116.edges  = (q_x29 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_117 = l_116.next   | l_117.edges  = (q_x29 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_118 = l_117.next   | l_118.edges  = (q_x29 -> q_s1) + (q_s1 -> q_s2) &&
	let l_119 = l_118.next   | l_119.edges  = (q_x29 -> q_s1) &&
	let l_120 = l_119.next   | l_120.edges  = (q_x30 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_121 = l_120.next   | l_121.edges  = (q_x30 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_122 = l_121.next   | l_122.edges  = (q_x30 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_123 = l_122.next   | l_123.edges  = (q_x30 -> q_s1) + (q_s1 -> q_s2) &&
	let l_124 = l_123.next   | l_124.edges  = (q_x30 -> q_s1) &&
	let l_125 = l_124.next   | l_125.edges  = (q_x31 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_126 = l_125.next   | l_126.edges  = (q_x31 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_127 = l_126.next   | l_127.edges  = (q_x31 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_128 = l_127.next   | l_128.edges  = (q_x31 -> q_s1) + (q_s1 -> q_s2) &&
	let l_129 = l_128.next   | l_129.edges  = (q_x31 -> q_s1) &&
	let l_130 = l_129.next   | l_130.edges  = (q_x32 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_131 = l_130.next   | l_131.edges  = (q_x32 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_132 = l_131.next   | l_132.edges  = (q_x32 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_133 = l_132.next   | l_133.edges  = (q_x32 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_134 = l_133.next   | l_134.edges  = (q_x32 -> q_s1) + (q_s1 -> q_s2) &&
	let l_135 = l_134.next   | l_135.edges  = (q_x32 -> q_s1) &&
	let l_136 = l_135.next   | l_136.edges  = (q_x33 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_137 = l_136.next   | l_137.edges  = (q_x33 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_138 = l_137.next   | l_138.edges  = (q_x33 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_139 = l_138.next   | l_139.edges  = (q_x33 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_140 = l_139.next   | l_140.edges  = (q_x33 -> q_s1) + (q_s1 -> q_s2) &&
	let l_141 = l_140.next   | l_141.edges  = (q_x33 -> q_s1) &&
	let l_142 = l_141.next   | l_142.edges  = (q_x34 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_143 = l_142.next   | l_143.edges  = (q_x34 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_144 = l_143.next   | l_144.edges  = (q_x34 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_145 = l_144.next   | l_145.edges  = (q_x34 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_146 = l_145.next   | l_146.edges  = (q_x34 -> q_s1) + (q_s1 -> q_s2) &&
	let l_147 = l_146.next   | l_147.edges  = (q_x34 -> q_s1) &&
	let l_148 = l_147.next   | l_148.edges  = (q_x35 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_149 = l_148.next   | l_149.edges  = (q_x35 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_150 = l_149.next   | l_150.edges  = (q_x35 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_151 = l_150.next   | l_151.edges  = (q_x35 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_152 = l_151.next   | l_152.edges  = (q_x35 -> q_s1) + (q_s1 -> q_s2) &&
	let l_153 = l_152.next   | l_153.edges  = (q_x35 -> q_s1) &&
	let l_154 = l_153.next   | l_154.edges  = (q_x36 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_155 = l_154.next   | l_155.edges  = (q_x36 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_156 = l_155.next   | l_156.edges  = (q_x36 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_157 = l_156.next   | l_157.edges  = (q_x36 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_158 = l_157.next   | l_158.edges  = (q_x36 -> q_s1) + (q_s1 -> q_s2) &&
	let l_159 = l_158.next   | l_159.edges  = (q_x36 -> q_s1) &&
	let l_160 = l_159.next   | l_160.edges  = (q_x37 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_161 = l_160.next   | l_161.edges  = (q_x37 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_162 = l_161.next   | l_162.edges  = (q_x37 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_163 = l_162.next   | l_163.edges  = (q_x37 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_164 = l_163.next   | l_164.edges  = (q_x37 -> q_s1) + (q_s1 -> q_s2) &&
	let l_165 = l_164.next   | l_165.edges  = (q_x37 -> q_s1) &&
	let l_166 = l_165.next   | l_166.edges  = (q_x38 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_167 = l_166.next   | l_167.edges  = (q_x38 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_168 = l_167.next   | l_168.edges  = (q_x38 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_169 = l_168.next   | l_169.edges  = (q_x38 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_170 = l_169.next   | l_170.edges  = (q_x38 -> q_s1) + (q_s1 -> q_s2) &&
	let l_171 = l_170.next   | l_171.edges  = (q_x38 -> q_s1) &&
	let l_172 = l_171.next   | l_172.edges  = (q_x39 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_173 = l_172.next   | l_173.edges  = (q_x39 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_174 = l_173.next   | l_174.edges  = (q_x39 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_175 = l_174.next   | l_175.edges  = (q_x39 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_176 = l_175.next   | l_176.edges  = (q_x39 -> q_s1) + (q_s1 -> q_s2) &&
	let l_177 = l_176.next   | l_177.edges  = (q_x39 -> q_s1) &&
	let l_178 = l_177.next   | l_178.edges  = (q_x40 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_179 = l_178.next   | l_179.edges  = (q_x40 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_180 = l_179.next   | l_180.edges  = (q_x40 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_181 = l_180.next   | l_181.edges  = (q_x40 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_182 = l_181.next   | l_182.edges  = (q_x40 -> q_s1) + (q_s1 -> q_s2) &&
	let l_183 = l_182.next   | l_183.edges  = (q_x40 -> q_s1) &&
	let l_184 = l_183.next   | l_184.edges  = (q_x41 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_185 = l_184.next   | l_185.edges  = (q_x41 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_186 = l_185.next   | l_186.edges  = (q_x41 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_187 = l_186.next   | l_187.edges  = (q_x41 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_188 = l_187.next   | l_188.edges  = (q_x41 -> q_s1) + (q_s1 -> q_s2) &&
	let l_189 = l_188.next   | l_189.edges  = (q_x41 -> q_s1) &&
	let l_190 = l_189.next   | l_190.edges  = (q_x42 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_191 = l_190.next   | l_191.edges  = (q_x42 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_192 = l_191.next   | l_192.edges  = (q_x42 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_193 = l_192.next   | l_193.edges  = (q_x42 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_194 = l_193.next   | l_194.edges  = (q_x42 -> q_s1) + (q_s1 -> q_s2) &&
	let l_195 = l_194.next   | l_195.edges  = (q_x42 -> q_s1) &&
	let l_196 = l_195.next   | l_196.edges  = (q_x43 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_197 = l_196.next   | l_197.edges  = (q_x43 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_198 = l_197.next   | l_198.edges  = (q_x43 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_199 = l_198.next   | l_199.edges  = (q_x43 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_200 = l_199.next   | l_200.edges  = (q_x43 -> q_s1) + (q_s1 -> q_s2) &&
	let l_201 = l_200.next   | l_201.edges  = (q_x43 -> q_s1) &&
	let l_202 = l_201.next   | l_202.edges  = (q_x44 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_203 = l_202.next   | l_203.edges  = (q_x44 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_204 = l_203.next   | l_204.edges  = (q_x44 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_205 = l_204.next   | l_205.edges  = (q_x44 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_206 = l_205.next   | l_206.edges  = (q_x44 -> q_s1) + (q_s1 -> q_s2) &&
	let l_207 = l_206.next   | l_207.edges  = (q_x44 -> q_s1) &&
	let l_208 = l_207.next   | l_208.edges  = (q_x45 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_209 = l_208.next   | l_209.edges  = (q_x45 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_210 = l_209.next   | l_210.edges  = (q_x45 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_211 = l_210.next   | l_211.edges  = (q_x45 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_212 = l_211.next   | l_212.edges  = (q_x45 -> q_s1) + (q_s1 -> q_s2) &&
	let l_213 = l_212.next   | l_213.edges  = (q_x45 -> q_s1) &&
	let l_214 = l_213.next   | l_214.edges  = (q_x46 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_215 = l_214.next   | l_215.edges  = (q_x46 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_216 = l_215.next   | l_216.edges  = (q_x46 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_217 = l_216.next   | l_217.edges  = (q_x46 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_218 = l_217.next   | l_218.edges  = (q_x46 -> q_s1) + (q_s1 -> q_s2) &&
	let l_219 = l_218.next   | l_219.edges  = (q_x46 -> q_s1) &&
	let l_220 = l_219.next   | l_220.edges  = (q_x47 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_221 = l_220.next   | l_221.edges  = (q_x47 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_222 = l_221.next   | l_222.edges  = (q_x47 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_223 = l_222.next   | l_223.edges  = (q_x47 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_224 = l_223.next   | l_224.edges  = (q_x47 -> q_s1) + (q_s1 -> q_s2) &&
	let l_225 = l_224.next   | l_225.edges  = (q_x47 -> q_s1) &&
	let l_226 = l_225.next   | l_226.edges  = (q_x48 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_227 = l_226.next   | l_227.edges  = (q_x48 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_228 = l_227.next   | l_228.edges  = (q_x48 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_229 = l_228.next   | l_229.edges  = (q_x48 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_230 = l_229.next   | l_230.edges  = (q_x48 -> q_s1) + (q_s1 -> q_s2) &&
	let l_231 = l_230.next   | l_231.edges  = (q_x48 -> q_s1) &&
	let l_232 = l_231.next   | l_232.edges  = (q_x49 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_233 = l_232.next   | l_233.edges  = (q_x49 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_234 = l_233.next   | l_234.edges  = (q_x49 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_235 = l_234.next   | l_235.edges  = (q_x49 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_236 = l_235.next   | l_236.edges  = (q_x49 -> q_s1) + (q_s1 -> q_s2) &&
	let l_237 = l_236.next   | l_237.edges  = (q_x49 -> q_s1) &&
	let l_238 = l_237.next   | l_238.edges  = (q_x50 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) + (q_s5 -> q_s6) &&
	let l_239 = l_238.next   | l_239.edges  = (q_x50 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) + (q_s4 -> q_s5) &&
	let l_240 = l_239.next   | l_240.edges  = (q_x50 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) + (q_s3 -> q_s4) &&
	let l_241 = l_240.next   | l_241.edges  = (q_x50 -> q_s1) + (q_s1 -> q_s2) + (q_s2 -> q_s3) &&
	let l_242 = l_241.next   | l_242.edges  = (q_x50 -> q_s1) + (q_s1 -> q_s2) &&
	let l_243 = l_242.next   | l_243.edges  = (q_x50 -> q_s1) &&
	let l_244 = l_243.next   | l_244.edges  = (q_s1 -> q_x1) + (q_x1 -> q_x2) &&
	let l_245 = l_244.next   | l_245.edges  = (q_s1 -> q_x3) + (q_x3 -> q_x4) &&
	let l_246 = l_245.next   | l_246.edges  = (q_s1 -> q_x5) + (q_x5 -> q_x6) &&
	let l_247 = l_246.next   | l_247.edges  = (q_s1 -> q_x7) + (q_x7 -> q_x8) &&
	let l_248 = l_247.next   | l_248.edges  = (q_s1 -> q_x9) + (q_x9 -> q_x10) &&
	let l_249 = l_248.next   | l_249.edges  = (q_s1 -> q_x11) + (q_x11 -> q_x12) &&
	let l_250 = l_249.next   | l_250.edges  = (q_s1 -> q_x13) + (q_x13 -> q_x14) &&
	let l_251 = l_250.next   | l_251.edges  = (q_s1 -> q_x15) + (q_x15 -> q_x16) &&
	let l_252 = l_251.next   | l_252.edges  = (q_s1 -> q_x17) + (q_x17 -> q_x18) &&
	let l_253 = l_252.next   | l_253.edges  = (q_s1 -> q_x19) + (q_x19 -> q_x20) &&
	let l_254 = l_253.next   | l_254.edges  = (q_s1 -> q_x21) + (q_x21 -> q_x22) &&
	let l_255 = l_254.next   | l_255.edges  = (q_s1 -> q_x23) + (q_x23 -> q_x24) &&
	let l_256 = l_255.next   | l_256.edges  = (q_s1 -> q_x25) + (q_x25 -> q_x26) &&
	let l_257 = l_256.next   | l_257.edges  = (q_s1 -> q_x27) + (q_x27 -> q_x28) &&
	let l_258 = l_257.next   | l_258.edges  = (q_s1 -> q_x29) + (q_x29 -> q_x30) &&
	let l_259 = l_258.next   | l_259.edges  = (q_s1 -> q_x31) + (q_x31 -> q_x32) &&
	let l_260 = l_259.next   | l_260.edges  = (q_s1 -> q_x33) + (q_x33 -> q_x34) &&
	let l_261 = l_260.next   | l_261.edges  = (q_s1 -> q_x35) + (q_x35 -> q_x36) &&
	let l_262 = l_261.next   | l_262.edges  = (q_s1 -> q_x37) + (q_x37 -> q_x38) &&
	let l_263 = l_262.next   | l_263.edges  = (q_s1 -> q_x39) + (q_x39 -> q_x40) &&
	let l_264 = l_263.next   | l_264.edges  = (q_s1 -> q_x41) + (q_x41 -> q_x42) &&
	let l_265 = l_264.next   | l_265.edges  = (q_s1 -> q_x43) + (q_x43 -> q_x44) &&
	let l_266 = l_265.next   | l_266.edges  = (q_s1 -> q_x45) + (q_x45 -> q_x46) &&
	let l_267 = l_266.next   | l_267.edges  = (q_s1 -> q_x47) + (q_x47 -> q_x48) &&
	let l_268 = l_267.next   | l_268.edges  = (q_s1 -> q_x49) + (q_x49 -> q_x50) &&
	let l_269 = l_268.next   | l_269.edges  = (q_s1 -> q_x1) + (q_x1 -> q_x3) &&
	let l_270 = l_269.next   | l_270.edges  = (q_s1 -> q_x5) + (q_x5 -> q_x7) &&
	let l_271 = l_270.next   | l_271.edges  = (q_s1 -> q_x9) + (q_x9 -> q_x11) &&
	let l_272 = l_271.next   | l_272.edges  = (q_s1 -> q_x13) + (q_x13 -> q_x15) &&
	let l_273 = l_272.next   | l_273.edges  = (q_s1 -> q_x17) + (q_x17 -> q_x19) &&
	let l_274 = l_273.next   | l_274.edges  = (q_s1 -> q_x21) + (q_x21 -> q_x23) &&
	let l_275 = l_274.next   | l_275.edges  = (q_s1 -> q_x25) + (q_x25 -> q_x27) &&
	let l_276 = l_275.next   | l_276.edges  = (q_s1 -> q_x29) + (q_x29 -> q_x31) &&
	let l_277 = l_276.next   | l_277.edges  = (q_s1 -> q_x33) + (q_x33 -> q_x35) &&
	let l_278 = l_277.next   | l_278.edges  = (q_s1 -> q_x37) + (q_x37 -> q_x39) &&
	let l_279 = l_278.next   | l_279.edges  = (q_s1 -> q_x41) + (q_x41 -> q_x43) &&
	let l_280 = l_279.next   | l_280.edges  = (q_s1 -> q_x45) + (q_x45 -> q_x47) &&
	let l_281 = l_280.next   | l_281.edges  = (q_s1 -> q_x49) + (q_x49 -> q_x1) &&
	let l_282 = l_281.next   | l_282.edges  = (q_s1 -> q_x5) + (q_x5 -> q_x9) &&
	let l_283 = l_282.next   | l_283.edges  = (q_s1 -> q_x13) + (q_x13 -> q_x17) &&
	let l_284 = l_283.next   | l_284.edges  = (q_s1 -> q_x21) + (q_x21 -> q_x25) &&
	let l_285 = l_284.next   | l_285.edges  = (q_s1 -> q_x29) + (q_x29 -> q_x33) &&
	let l_286 = l_285.next   | l_286.edges  = (q_s1 -> q_x37) + (q_x37 -> q_x41) &&
	let l_287 = l_286.next   | l_287.edges  = (q_s1 -> q_x45) + (q_x45 -> q_x49) &&
	let l_288 = l_287.next   | l_288.edges  = (q_s1 -> q_x5) + (q_x5 -> q_x13) &&
	let l_289 = l_288.next   | l_289.edges  = (q_s1 -> q_x21) + (q_x21 -> q_x29) &&
	let l_290 = l_289.next   | l_290.edges  = (q_s1 -> q_x37) + (q_x37 -> q_x45) &&
	let l_291 = l_290.next   | l_291.edges  = (q_s1 -> q_x5) + (q_x5 -> q_x21) &&
	let l_292 = l_291.next   | l_292.edges  = (q_s1 -> q_x37) + (q_x37 -> q_x5) +
                                                  (q_s2 -> q_x1) + (q_x1 -> q_x3) &&
	let l_293 = l_292.next   | l_293.edges  = (q_s2 -> q_x2) + (q_x2 -> q_x4) &&
	let l_294 = l_293.next   | l_294.edges  = (q_s2 -> q_x5) + (q_x5 -> q_x7) &&
	let l_295 = l_294.next   | l_295.edges  = (q_s2 -> q_x6) + (q_x6 -> q_x8) &&
	let l_296 = l_295.next   | l_296.edges  = (q_s2 -> q_x9) + (q_x9 -> q_x11) &&
	let l_297 = l_296.next   | l_297.edges  = (q_s2 -> q_x10) + (q_x10 -> q_x12) &&
	let l_298 = l_297.next   | l_298.edges  = (q_s2 -> q_x13) + (q_x13 -> q_x15) &&
	let l_299 = l_298.next   | l_299.edges  = (q_s2 -> q_x14) + (q_x14 -> q_x16) &&
	let l_300 = l_299.next   | l_300.edges  = (q_s2 -> q_x17) + (q_x17 -> q_x19) &&
	let l_301 = l_300.next   | l_301.edges  = (q_s2 -> q_x18) + (q_x18 -> q_x20) &&
	let l_302 = l_301.next   | l_302.edges  = (q_s2 -> q_x21) + (q_x21 -> q_x23) &&
	let l_303 = l_302.next   | l_303.edges  = (q_s2 -> q_x22) + (q_x22 -> q_x24) &&
	let l_304 = l_303.next   | l_304.edges  = (q_s2 -> q_x25) + (q_x25 -> q_x27) &&
	let l_305 = l_304.next   | l_305.edges  = (q_s2 -> q_x26) + (q_x26 -> q_x28) &&
	let l_306 = l_305.next   | l_306.edges  = (q_s2 -> q_x29) + (q_x29 -> q_x31) &&
	let l_307 = l_306.next   | l_307.edges  = (q_s2 -> q_x30) + (q_x30 -> q_x32) &&
	let l_308 = l_307.next   | l_308.edges  = (q_s2 -> q_x33) + (q_x33 -> q_x35) &&
	let l_309 = l_308.next   | l_309.edges  = (q_s2 -> q_x34) + (q_x34 -> q_x36) &&
	let l_310 = l_309.next   | l_310.edges  = (q_s2 -> q_x37) + (q_x37 -> q_x39) &&
	let l_311 = l_310.next   | l_311.edges  = (q_s2 -> q_x38) + (q_x38 -> q_x40) &&
	let l_312 = l_311.next   | l_312.edges  = (q_s2 -> q_x41) + (q_x41 -> q_x43) &&
	let l_313 = l_312.next   | l_313.edges  = (q_s2 -> q_x42) + (q_x42 -> q_x44) &&
	let l_314 = l_313.next   | l_314.edges  = (q_s2 -> q_x45) + (q_x45 -> q_x47) &&
	let l_315 = l_314.next   | l_315.edges  = (q_s2 -> q_x46) + (q_x46 -> q_x48) &&
	let l_316 = l_315.next   | l_316.edges  = (q_s2 -> q_x49) + (q_x49 -> q_x1) &&
	let l_317 = l_316.next   | l_317.edges  = (q_s2 -> q_x50) + (q_x50 -> q_x2) &&
	let l_318 = l_317.next   | l_318.edges  = (q_s2 -> q_x5) + (q_x5 -> q_x9) &&
	let l_319 = l_318.next   | l_319.edges  = (q_s2 -> q_x6) + (q_x6 -> q_x10) &&
	let l_320 = l_319.next   | l_320.edges  = (q_s2 -> q_x13) + (q_x13 -> q_x17) &&
	let l_321 = l_320.next   | l_321.edges  = (q_s2 -> q_x14) + (q_x14 -> q_x18) &&
	let l_322 = l_321.next   | l_322.edges  = (q_s2 -> q_x21) + (q_x21 -> q_x25) &&
	let l_323 = l_322.next   | l_323.edges  = (q_s2 -> q_x22) + (q_x22 -> q_x26) &&
	let l_324 = l_323.next   | l_324.edges  = (q_s2 -> q_x29) + (q_x29 -> q_x33) &&
	let l_325 = l_324.next   | l_325.edges  = (q_s2 -> q_x30) + (q_x30 -> q_x34) &&
	let l_326 = l_325.next   | l_326.edges  = (q_s2 -> q_x37) + (q_x37 -> q_x41) &&
	let l_327 = l_326.next   | l_327.edges  = (q_s2 -> q_x38) + (q_x38 -> q_x42) &&
	let l_328 = l_327.next   | l_328.edges  = (q_s2 -> q_x45) + (q_x45 -> q_x49) &&
	let l_329 = l_328.next   | l_329.edges  = (q_s2 -> q_x46) + (q_x46 -> q_x50) &&
	let l_330 = l_329.next   | l_330.edges  = (q_s2 -> q_x5) + (q_x5 -> q_x13) &&
	let l_331 = l_330.next   | l_331.edges  = (q_s2 -> q_x6) + (q_x6 -> q_x14) &&
	let l_332 = l_331.next   | l_332.edges  = (q_s2 -> q_x21) + (q_x21 -> q_x29) &&
	let l_333 = l_332.next   | l_333.edges  = (q_s2 -> q_x22) + (q_x22 -> q_x30) &&
	let l_334 = l_333.next   | l_334.edges  = (q_s2 -> q_x37) + (q_x37 -> q_x45) &&
	let l_335 = l_334.next   | l_335.edges  = (q_s2 -> q_x38) + (q_x38 -> q_x46) &&
	let l_336 = l_335.next   | l_336.edges  = (q_s2 -> q_x5) + (q_x5 -> q_x21) &&
	let l_337 = l_336.next   | l_337.edges  = (q_s2 -> q_x6) + (q_x6 -> q_x22) &&
	let l_338 = l_337.next   | l_338.edges  = (q_s2 -> q_x37) + (q_x37 -> q_x5) &&
	let l_339 = l_338.next   | l_339.edges  = (q_s2 -> q_x38) + (q_x38 -> q_x6) +
                                                  (q_s3 -> q_x1) + (q_x1 -> q_x5) &&
	let l_340 = l_339.next   | l_340.edges  = (q_s3 -> q_x2) + (q_x2 -> q_x6) &&
	let l_341 = l_340.next   | l_341.edges  = (q_s3 -> q_x3) + (q_x3 -> q_x7) &&
	let l_342 = l_341.next   | l_342.edges  = (q_s3 -> q_x4) + (q_x4 -> q_x8) &&
	let l_343 = l_342.next   | l_343.edges  = (q_s3 -> q_x9) + (q_x9 -> q_x13) &&
	let l_344 = l_343.next   | l_344.edges  = (q_s3 -> q_x10) + (q_x10 -> q_x14) &&
	let l_345 = l_344.next   | l_345.edges  = (q_s3 -> q_x11) + (q_x11 -> q_x15) &&
	let l_346 = l_345.next   | l_346.edges  = (q_s3 -> q_x12) + (q_x12 -> q_x16) &&
	let l_347 = l_346.next   | l_347.edges  = (q_s3 -> q_x17) + (q_x17 -> q_x21) &&
	let l_348 = l_347.next   | l_348.edges  = (q_s3 -> q_x18) + (q_x18 -> q_x22) &&
	let l_349 = l_348.next   | l_349.edges  = (q_s3 -> q_x19) + (q_x19 -> q_x23) &&
	let l_350 = l_349.next   | l_350.edges  = (q_s3 -> q_x20) + (q_x20 -> q_x24) &&
	let l_351 = l_350.next   | l_351.edges  = (q_s3 -> q_x25) + (q_x25 -> q_x29) &&
	let l_352 = l_351.next   | l_352.edges  = (q_s3 -> q_x26) + (q_x26 -> q_x30) &&
	let l_353 = l_352.next   | l_353.edges  = (q_s3 -> q_x27) + (q_x27 -> q_x31) &&
	let l_354 = l_353.next   | l_354.edges  = (q_s3 -> q_x28) + (q_x28 -> q_x32) &&
	let l_355 = l_354.next   | l_355.edges  = (q_s3 -> q_x33) + (q_x33 -> q_x37) &&
	let l_356 = l_355.next   | l_356.edges  = (q_s3 -> q_x34) + (q_x34 -> q_x38) &&
	let l_357 = l_356.next   | l_357.edges  = (q_s3 -> q_x35) + (q_x35 -> q_x39) &&
	let l_358 = l_357.next   | l_358.edges  = (q_s3 -> q_x36) + (q_x36 -> q_x40) &&
	let l_359 = l_358.next   | l_359.edges  = (q_s3 -> q_x41) + (q_x41 -> q_x45) &&
	let l_360 = l_359.next   | l_360.edges  = (q_s3 -> q_x42) + (q_x42 -> q_x46) &&
	let l_361 = l_360.next   | l_361.edges  = (q_s3 -> q_x43) + (q_x43 -> q_x47) &&
	let l_362 = l_361.next   | l_362.edges  = (q_s3 -> q_x44) + (q_x44 -> q_x48) &&
	let l_363 = l_362.next   | l_363.edges  = (q_s3 -> q_x49) + (q_x49 -> q_x3) &&
	let l_364 = l_363.next   | l_364.edges  = (q_s3 -> q_x50) + (q_x50 -> q_x4) &&
	let l_365 = l_364.next   | l_365.edges  = (q_s3 -> q_x1) + (q_x1 -> q_x9) &&
	let l_366 = l_365.next   | l_366.edges  = (q_s3 -> q_x2) + (q_x2 -> q_x10) &&
	let l_367 = l_366.next   | l_367.edges  = (q_s3 -> q_x11) + (q_x11 -> q_x19) &&
	let l_368 = l_367.next   | l_368.edges  = (q_s3 -> q_x12) + (q_x12 -> q_x20) &&
	let l_369 = l_368.next   | l_369.edges  = (q_s3 -> q_x17) + (q_x17 -> q_x25) &&
	let l_370 = l_369.next   | l_370.edges  = (q_s3 -> q_x18) + (q_x18 -> q_x26) &&
	let l_371 = l_370.next   | l_371.edges  = (q_s3 -> q_x27) + (q_x27 -> q_x35) &&
	let l_372 = l_371.next   | l_372.edges  = (q_s3 -> q_x28) + (q_x28 -> q_x36) &&
	let l_373 = l_372.next   | l_373.edges  = (q_s3 -> q_x33) + (q_x33 -> q_x41) &&
	let l_374 = l_373.next   | l_374.edges  = (q_s3 -> q_x34) + (q_x34 -> q_x42) &&
	let l_375 = l_374.next   | l_375.edges  = (q_s3 -> q_x43) + (q_x43 -> q_x1) &&
	let l_376 = l_375.next   | l_376.edges  = (q_s3 -> q_x44) + (q_x44 -> q_x2) &&
	let l_377 = l_376.next   | l_377.edges  = (q_s3 -> q_x49) + (q_x49 -> q_x11) &&
	let l_378 = l_377.next   | l_378.edges  = (q_s3 -> q_x50) + (q_x50 -> q_x12) &&
	let l_379 = l_378.next   | l_379.edges  = (q_s3 -> q_x17) + (q_x17 -> q_x33) &&
	let l_380 = l_379.next   | l_380.edges  = (q_s3 -> q_x18) + (q_x18 -> q_x34) &&
	let l_381 = l_380.next   | l_381.edges  = (q_s3 -> q_x27) + (q_x27 -> q_x43) &&
	let l_382 = l_381.next   | l_382.edges  = (q_s3 -> q_x28) + (q_x28 -> q_x44) &&
	let l_383 = l_382.next   | l_383.edges  = (q_s3 -> q_x49) + (q_x49 -> q_x27) &&
	let l_384 = l_383.next   | l_384.edges  = (q_s3 -> q_x50) + (q_x50 -> q_x28) &&
	let l_385 = l_384.next   | l_385.edges  = (q_s3 -> q_x17) + (q_x17 -> q_x49) &&
	let l_386 = l_385.next   | l_386.edges  = (q_s3 -> q_x18) + (q_x18 -> q_x50) +
                                                  (q_s4 -> q_x1) + (q_x1 -> q_x9) &&
	let l_387 = l_386.next   | l_387.edges  = (q_s4 -> q_x2) + (q_x2 -> q_x10) &&
	let l_388 = l_387.next   | l_388.edges  = (q_s4 -> q_x3) + (q_x3 -> q_x11) &&
	let l_389 = l_388.next   | l_389.edges  = (q_s4 -> q_x4) + (q_x4 -> q_x12) &&
	let l_390 = l_389.next   | l_390.edges  = (q_s4 -> q_x5) + (q_x5 -> q_x13) &&
	let l_391 = l_390.next   | l_391.edges  = (q_s4 -> q_x6) + (q_x6 -> q_x14) &&
	let l_392 = l_391.next   | l_392.edges  = (q_s4 -> q_x7) + (q_x7 -> q_x15) &&
	let l_393 = l_392.next   | l_393.edges  = (q_s4 -> q_x8) + (q_x8 -> q_x16) &&
	let l_394 = l_393.next   | l_394.edges  = (q_s4 -> q_x17) + (q_x17 -> q_x25) &&
	let l_395 = l_394.next   | l_395.edges  = (q_s4 -> q_x18) + (q_x18 -> q_x26) &&
	let l_396 = l_395.next   | l_396.edges  = (q_s4 -> q_x19) + (q_x19 -> q_x27) &&
	let l_397 = l_396.next   | l_397.edges  = (q_s4 -> q_x20) + (q_x20 -> q_x28) &&
	let l_398 = l_397.next   | l_398.edges  = (q_s4 -> q_x21) + (q_x21 -> q_x29) &&
	let l_399 = l_398.next   | l_399.edges  = (q_s4 -> q_x22) + (q_x22 -> q_x30) &&
	let l_400 = l_399.next   | l_400.edges  = (q_s4 -> q_x23) + (q_x23 -> q_x31) &&
	let l_401 = l_400.next   | l_401.edges  = (q_s4 -> q_x24) + (q_x24 -> q_x32) &&
	let l_402 = l_401.next   | l_402.edges  = (q_s4 -> q_x33) + (q_x33 -> q_x41) &&
	let l_403 = l_402.next   | l_403.edges  = (q_s4 -> q_x34) + (q_x34 -> q_x42) &&
	let l_404 = l_403.next   | l_404.edges  = (q_s4 -> q_x35) + (q_x35 -> q_x43) &&
	let l_405 = l_404.next   | l_405.edges  = (q_s4 -> q_x36) + (q_x36 -> q_x44) &&
	let l_406 = l_405.next   | l_406.edges  = (q_s4 -> q_x37) + (q_x37 -> q_x45) &&
	let l_407 = l_406.next   | l_407.edges  = (q_s4 -> q_x38) + (q_x38 -> q_x46) &&
	let l_408 = l_407.next   | l_408.edges  = (q_s4 -> q_x39) + (q_x39 -> q_x47) &&
	let l_409 = l_408.next   | l_409.edges  = (q_s4 -> q_x40) + (q_x40 -> q_x48) &&
	let l_410 = l_409.next   | l_410.edges  = (q_s4 -> q_x49) + (q_x49 -> q_x7) &&
	let l_411 = l_410.next   | l_411.edges  = (q_s4 -> q_x50) + (q_x50 -> q_x8) &&
	let l_412 = l_411.next   | l_412.edges  = (q_s4 -> q_x1) + (q_x1 -> q_x17) &&
	let l_413 = l_412.next   | l_413.edges  = (q_s4 -> q_x2) + (q_x2 -> q_x18) &&
	let l_414 = l_413.next   | l_414.edges  = (q_s4 -> q_x3) + (q_x3 -> q_x19) &&
	let l_415 = l_414.next   | l_415.edges  = (q_s4 -> q_x4) + (q_x4 -> q_x20) &&
	let l_416 = l_415.next   | l_416.edges  = (q_s4 -> q_x5) + (q_x5 -> q_x21) &&
	let l_417 = l_416.next   | l_417.edges  = (q_s4 -> q_x6) + (q_x6 -> q_x22) &&
	let l_418 = l_417.next   | l_418.edges  = (q_s4 -> q_x23) + (q_x23 -> q_x39) &&
	let l_419 = l_418.next   | l_419.edges  = (q_s4 -> q_x24) + (q_x24 -> q_x40) &&
	let l_420 = l_419.next   | l_420.edges  = (q_s4 -> q_x33) + (q_x33 -> q_x49) &&
	let l_421 = l_420.next   | l_421.edges  = (q_s4 -> q_x34) + (q_x34 -> q_x50) &&
	let l_422 = l_421.next   | l_422.edges  = (q_s4 -> q_x35) + (q_x35 -> q_x1) &&
	let l_423 = l_422.next   | l_423.edges  = (q_s4 -> q_x36) + (q_x36 -> q_x2) &&
	let l_424 = l_423.next   | l_424.edges  = (q_s4 -> q_x37) + (q_x37 -> q_x3) &&
	let l_425 = l_424.next   | l_425.edges  = (q_s4 -> q_x38) + (q_x38 -> q_x4) &&
	let l_426 = l_425.next   | l_426.edges  = (q_s4 -> q_x5) + (q_x5 -> q_x37) &&
	let l_427 = l_426.next   | l_427.edges  = (q_s4 -> q_x6) + (q_x6 -> q_x38) &&
	let l_428 = l_427.next   | l_428.edges  = (q_s4 -> q_x23) + (q_x23 -> q_x5) &&
	let l_429 = l_428.next   | l_429.edges  = (q_s4 -> q_x24) + (q_x24 -> q_x6) &&
	let l_430 = l_429.next   | l_430.edges  = (q_s4 -> q_x33) + (q_x33 -> q_x23) &&
	let l_431 = l_430.next   | l_431.edges  = (q_s4 -> q_x34) + (q_x34 -> q_x24) &&
	let l_432 = l_431.next   | l_432.edges  = (q_s4 -> q_x35) + (q_x35 -> q_x33) &&
	let l_433 = l_432.next   | l_433.edges  = (q_s4 -> q_x36) + (q_x36 -> q_x34) +
                                                  (q_s5 -> q_x1) + (q_x1 -> q_x17) &&
	let l_434 = l_433.next   | l_434.edges  = (q_s5 -> q_x2) + (q_x2 -> q_x18) &&
	let l_435 = l_434.next   | l_435.edges  = (q_s5 -> q_x3) + (q_x3 -> q_x19) &&
	let l_436 = l_435.next   | l_436.edges  = (q_s5 -> q_x4) + (q_x4 -> q_x20) &&
	let l_437 = l_436.next   | l_437.edges  = (q_s5 -> q_x5) + (q_x5 -> q_x21) &&
	let l_438 = l_437.next   | l_438.edges  = (q_s5 -> q_x6) + (q_x6 -> q_x22) &&
	let l_439 = l_438.next   | l_439.edges  = (q_s5 -> q_x7) + (q_x7 -> q_x23) &&
	let l_440 = l_439.next   | l_440.edges  = (q_s5 -> q_x8) + (q_x8 -> q_x24) &&
	let l_441 = l_440.next   | l_441.edges  = (q_s5 -> q_x9) + (q_x9 -> q_x25) &&
	let l_442 = l_441.next   | l_442.edges  = (q_s5 -> q_x10) + (q_x10 -> q_x26) &&
	let l_443 = l_442.next   | l_443.edges  = (q_s5 -> q_x11) + (q_x11 -> q_x27) &&
	let l_444 = l_443.next   | l_444.edges  = (q_s5 -> q_x12) + (q_x12 -> q_x28) &&
	let l_445 = l_444.next   | l_445.edges  = (q_s5 -> q_x13) + (q_x13 -> q_x29) &&
	let l_446 = l_445.next   | l_446.edges  = (q_s5 -> q_x14) + (q_x14 -> q_x30) &&
	let l_447 = l_446.next   | l_447.edges  = (q_s5 -> q_x15) + (q_x15 -> q_x31) &&
	let l_448 = l_447.next   | l_448.edges  = (q_s5 -> q_x16) + (q_x16 -> q_x32) &&
	let l_449 = l_448.next   | l_449.edges  = (q_s5 -> q_x33) + (q_x33 -> q_x49) &&
	let l_450 = l_449.next   | l_450.edges  = (q_s5 -> q_x34) + (q_x34 -> q_x50) &&
	let l_451 = l_450.next   | l_451.edges  = (q_s5 -> q_x35) + (q_x35 -> q_x1) &&
	let l_452 = l_451.next   | l_452.edges  = (q_s5 -> q_x36) + (q_x36 -> q_x2) &&
	let l_453 = l_452.next   | l_453.edges  = (q_s5 -> q_x37) + (q_x37 -> q_x3) &&
	let l_454 = l_453.next   | l_454.edges  = (q_s5 -> q_x38) + (q_x38 -> q_x4) &&
	let l_455 = l_454.next   | l_455.edges  = (q_s5 -> q_x39) + (q_x39 -> q_x5) &&
	let l_456 = l_455.next   | l_456.edges  = (q_s5 -> q_x40) + (q_x40 -> q_x6) &&
	let l_457 = l_456.next   | l_457.edges  = (q_s5 -> q_x41) + (q_x41 -> q_x7) &&
	let l_458 = l_457.next   | l_458.edges  = (q_s5 -> q_x42) + (q_x42 -> q_x8) &&
	let l_459 = l_458.next   | l_459.edges  = (q_s5 -> q_x43) + (q_x43 -> q_x9) &&
	let l_460 = l_459.next   | l_460.edges  = (q_s5 -> q_x44) + (q_x44 -> q_x10) &&
	let l_461 = l_460.next   | l_461.edges  = (q_s5 -> q_x45) + (q_x45 -> q_x11) &&
	let l_462 = l_461.next   | l_462.edges  = (q_s5 -> q_x46) + (q_x46 -> q_x12) &&
	let l_463 = l_462.next   | l_463.edges  = (q_s5 -> q_x47) + (q_x47 -> q_x13) &&
	let l_464 = l_463.next   | l_464.edges  = (q_s5 -> q_x48) + (q_x48 -> q_x14) &&
	let l_465 = l_464.next   | l_465.edges  = (q_s5 -> q_x15) + (q_x15 -> q_x47) &&
	let l_466 = l_465.next   | l_466.edges  = (q_s5 -> q_x16) + (q_x16 -> q_x48) &&
	let l_467 = l_466.next   | l_467.edges  = (q_s5 -> q_x33) + (q_x33 -> q_x15) &&
	let l_468 = l_467.next   | l_468.edges  = (q_s5 -> q_x34) + (q_x34 -> q_x16) &&
	let l_469 = l_468.next   | l_469.edges  = (q_s5 -> q_x35) + (q_x35 -> q_x33) &&
	let l_470 = l_469.next   | l_470.edges  = (q_s5 -> q_x36) + (q_x36 -> q_x34) &&
	let l_471 = l_470.next   | l_471.edges  = (q_s5 -> q_x37) + (q_x37 -> q_x35) &&
	let l_472 = l_471.next   | l_472.edges  = (q_s5 -> q_x38) + (q_x38 -> q_x36) &&
	let l_473 = l_472.next   | l_473.edges  = (q_s5 -> q_x39) + (q_x39 -> q_x37) &&
	let l_474 = l_473.next   | l_474.edges  = (q_s5 -> q_x40) + (q_x40 -> q_x38) &&
	let l_475 = l_474.next   | l_475.edges  = (q_s5 -> q_x41) + (q_x41 -> q_x39) &&
	let l_476 = l_475.next   | l_476.edges  = (q_s5 -> q_x42) + (q_x42 -> q_x40) &&
	let l_477 = l_476.next   | l_477.edges  = (q_s5 -> q_x43) + (q_x43 -> q_x41) &&
	let l_478 = l_477.next   | l_478.edges  = (q_s5 -> q_x44) + (q_x44 -> q_x42) &&
	let l_479 = l_478.next   | l_479.edges  = (q_s5 -> q_x45) + (q_x45 -> q_x43) &&
	let l_480 = l_479.next   | l_480.edges  = (q_s5 -> q_x46) + (q_x46 -> q_x44) +
                                                  (q_s6 -> q_x1) + (q_x1 -> q_x33) &&
	let l_481 = l_480.next   | l_481.edges  = (q_s6 -> q_x2) + (q_x2 -> q_x34) &&
	let l_482 = l_481.next   | l_482.edges  = (q_s6 -> q_x3) + (q_x3 -> q_x35) &&
	let l_483 = l_482.next   | l_483.edges  = (q_s6 -> q_x4) + (q_x4 -> q_x36) &&
	let l_484 = l_483.next   | l_484.edges  = (q_s6 -> q_x5) + (q_x5 -> q_x37) &&
	let l_485 = l_484.next   | l_485.edges  = (q_s6 -> q_x6) + (q_x6 -> q_x38) &&
	let l_486 = l_485.next   | l_486.edges  = (q_s6 -> q_x7) + (q_x7 -> q_x39) &&
	let l_487 = l_486.next   | l_487.edges  = (q_s6 -> q_x8) + (q_x8 -> q_x40) &&
	let l_488 = l_487.next   | l_488.edges  = (q_s6 -> q_x9) + (q_x9 -> q_x41) &&
	let l_489 = l_488.next   | l_489.edges  = (q_s6 -> q_x10) + (q_x10 -> q_x42) &&
	let l_490 = l_489.next   | l_490.edges  = (q_s6 -> q_x11) + (q_x11 -> q_x43) &&
	let l_491 = l_490.next   | l_491.edges  = (q_s6 -> q_x12) + (q_x12 -> q_x44) &&
	let l_492 = l_491.next   | l_492.edges  = (q_s6 -> q_x13) + (q_x13 -> q_x45) &&
	let l_493 = l_492.next   | l_493.edges  = (q_s6 -> q_x14) + (q_x14 -> q_x46) &&
	let l_494 = l_493.next   | l_494.edges  = (q_s6 -> q_x15) + (q_x15 -> q_x47) &&
	let l_495 = l_494.next   | l_495.edges  = (q_s6 -> q_x16) + (q_x16 -> q_x48) &&
	let l_496 = l_495.next   | l_496.edges  = (q_s6 -> q_x17) + (q_x17 -> q_x49) &&
	let l_497 = l_496.next   | l_497.edges  = (q_s6 -> q_x18) + (q_x18 -> q_x50) &&
	let l_498 = l_497.next   | l_498.edges  = (q_s6 -> q_x19) + (q_x19 -> q_x1) &&
	let l_499 = l_498.next   | l_499.edges  = (q_s6 -> q_x20) + (q_x20 -> q_x2) &&
	let l_500 = l_499.next   | l_500.edges  = (q_s6 -> q_x21) + (q_x21 -> q_x3) &&
	let l_501 = l_500.next   | l_501.edges  = (q_s6 -> q_x22) + (q_x22 -> q_x4) &&
	let l_502 = l_501.next   | l_502.edges  = (q_s6 -> q_x23) + (q_x23 -> q_x5) &&
	let l_503 = l_502.next   | l_503.edges  = (q_s6 -> q_x24) + (q_x24 -> q_x6) &&
	let l_504 = l_503.next   | l_504.edges  = (q_s6 -> q_x25) + (q_x25 -> q_x7) &&
	let l_505 = l_504.next   | l_505.edges  = (q_s6 -> q_x26) + (q_x26 -> q_x8) &&
	let l_506 = l_505.next   | l_506.edges  = (q_s6 -> q_x27) + (q_x27 -> q_x9) &&
	let l_507 = l_506.next   | l_507.edges  = (q_s6 -> q_x28) + (q_x28 -> q_x10) &&
	let l_508 = l_507.next   | l_508.edges  = (q_s6 -> q_x29) + (q_x29 -> q_x11) &&
	let l_509 = l_508.next   | l_509.edges  = (q_s6 -> q_x30) + (q_x30 -> q_x12) &&
	let l_510 = l_509.next   | l_510.edges  = (q_s6 -> q_x31) + (q_x31 -> q_x13) &&
	let l_511 = l_510.next   | l_511.edges  = (q_s6 -> q_x32) + (q_x32 -> q_x14) &&
	let l_512 = l_511.next   | l_512.edges  = (q_s6 -> q_x15) + (q_x15 -> q_x29) &&
	let l_513 = l_512.next   | l_513.edges  = (q_s6 -> q_x16) + (q_x16 -> q_x30) &&
	let l_514 = l_513.next   | l_514.edges  = (q_s6 -> q_x17) + (q_x17 -> q_x31) &&
	let l_515 = l_514.next   | l_515.edges  = (q_s6 -> q_x18) + (q_x18 -> q_x32) &&
	let l_516 = l_515.next   | l_516.edges  = (q_s6 -> q_x19) + (q_x19 -> q_x15) &&
	let l_517 = l_516.next   | l_517.edges  = (q_s6 -> q_x20) + (q_x20 -> q_x16) &&
	let l_518 = l_517.next   | l_518.edges  = (q_s6 -> q_x21) + (q_x21 -> q_x17) &&
	let l_519 = l_518.next   | l_519.edges  = (q_s6 -> q_x22) + (q_x22 -> q_x18) &&
	let l_520 = l_519.next   | l_520.edges  = (q_s6 -> q_x23) + (q_x23 -> q_x19) &&
	let l_521 = l_520.next   | l_521.edges  = (q_s6 -> q_x24) + (q_x24 -> q_x20) &&
	let l_522 = l_521.next   | l_522.edges  = (q_s6 -> q_x25) + (q_x25 -> q_x21) &&
	let l_523 = l_522.next   | l_523.edges  = (q_s6 -> q_x26) + (q_x26 -> q_x22) &&
	let l_524 = l_523.next   | l_524.edges  = (q_s6 -> q_x27) + (q_x27 -> q_x23) &&
	let l_525 = l_524.next   | l_525.edges  = (q_s6 -> q_x28) + (q_x28 -> q_x24) &&
	let l_526 = l_525.next   | l_526.edges  = (q_s6 -> q_x25) + (q_x25 -> q_x27) &&
	let l_527 = l_526.next   | l_527.edges  = (q_s6 -> q_x26) + (q_x26 -> q_x28)
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

run finalLayer for 528 circGraph, 16 Int
