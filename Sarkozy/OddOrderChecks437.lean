import Sarkozy.OddOrderChunks437.Chunk19
import Sarkozy.OddOrderChunkLemma

/-!
# Every row of the actual 437 order certificate is checked

The generic block-concatenation theorem combines the independently checked
source and target chunks without reevaluating their certificate computations.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Sarkozy.OddOrder437

open OddOrder

noncomputable section

theorem sources_checked : allIndexed (sourceCheck 19 23 3 G19 G23 endpointTable) 0 rows = true := by
  apply allIndexed_of_blocks (P := sourceCheck 19 23 3 G19 G23 endpointTable)
    (rows := rows) (b := 128) (c := 154) (by decide) (by rw [rows_size]; decide)
  intro i
  fin_cases i
  · exact source_chunk_00
  · exact source_chunk_01
  · exact source_chunk_02
  · exact source_chunk_03
  · exact source_chunk_04
  · exact source_chunk_05
  · exact source_chunk_06
  · exact source_chunk_07
  · exact source_chunk_08
  · exact source_chunk_09
  · exact source_chunk_10
  · exact source_chunk_11
  · exact source_chunk_12
  · exact source_chunk_13
  · exact source_chunk_14
  · exact source_chunk_15
  · exact source_chunk_16
  · exact source_chunk_17
  · exact source_chunk_18
  · exact source_chunk_19
  · exact source_chunk_20
  · exact source_chunk_21
  · exact source_chunk_22
  · exact source_chunk_23
  · exact source_chunk_24
  · exact source_chunk_25
  · exact source_chunk_26
  · exact source_chunk_27
  · exact source_chunk_28
  · exact source_chunk_29
  · exact source_chunk_30
  · exact source_chunk_31
  · exact source_chunk_32
  · exact source_chunk_33
  · exact source_chunk_34
  · exact source_chunk_35
  · exact source_chunk_36
  · exact source_chunk_37
  · exact source_chunk_38
  · exact source_chunk_39
  · exact source_chunk_40
  · exact source_chunk_41
  · exact source_chunk_42
  · exact source_chunk_43
  · exact source_chunk_44
  · exact source_chunk_45
  · exact source_chunk_46
  · exact source_chunk_47
  · exact source_chunk_48
  · exact source_chunk_49
  · exact source_chunk_50
  · exact source_chunk_51
  · exact source_chunk_52
  · exact source_chunk_53
  · exact source_chunk_54
  · exact source_chunk_55
  · exact source_chunk_56
  · exact source_chunk_57
  · exact source_chunk_58
  · exact source_chunk_59
  · exact source_chunk_60
  · exact source_chunk_61
  · exact source_chunk_62
  · exact source_chunk_63
  · exact source_chunk_64
  · exact source_chunk_65
  · exact source_chunk_66
  · exact source_chunk_67
  · exact source_chunk_68
  · exact source_chunk_69
  · exact source_chunk_70
  · exact source_chunk_71
  · exact source_chunk_72
  · exact source_chunk_73
  · exact source_chunk_74
  · exact source_chunk_75
  · exact source_chunk_76
  · exact source_chunk_77
  · exact source_chunk_78
  · exact source_chunk_79
  · exact source_chunk_80
  · exact source_chunk_81
  · exact source_chunk_82
  · exact source_chunk_83
  · exact source_chunk_84
  · exact source_chunk_85
  · exact source_chunk_86
  · exact source_chunk_87
  · exact source_chunk_88
  · exact source_chunk_89
  · exact source_chunk_90
  · exact source_chunk_91
  · exact source_chunk_92
  · exact source_chunk_93
  · exact source_chunk_94
  · exact source_chunk_95
  · exact source_chunk_96
  · exact source_chunk_97
  · exact source_chunk_98
  · exact source_chunk_99
  · exact source_chunk_100
  · exact source_chunk_101
  · exact source_chunk_102
  · exact source_chunk_103
  · exact source_chunk_104
  · exact source_chunk_105
  · exact source_chunk_106
  · exact source_chunk_107
  · exact source_chunk_108
  · exact source_chunk_109
  · exact source_chunk_110
  · exact source_chunk_111
  · exact source_chunk_112
  · exact source_chunk_113
  · exact source_chunk_114
  · exact source_chunk_115
  · exact source_chunk_116
  · exact source_chunk_117
  · exact source_chunk_118
  · exact source_chunk_119
  · exact source_chunk_120
  · exact source_chunk_121
  · exact source_chunk_122
  · exact source_chunk_123
  · exact source_chunk_124
  · exact source_chunk_125
  · exact source_chunk_126
  · exact source_chunk_127
  · exact source_chunk_128
  · exact source_chunk_129
  · exact source_chunk_130
  · exact source_chunk_131
  · exact source_chunk_132
  · exact source_chunk_133
  · exact source_chunk_134
  · exact source_chunk_135
  · exact source_chunk_136
  · exact source_chunk_137
  · exact source_chunk_138
  · exact source_chunk_139
  · exact source_chunk_140
  · exact source_chunk_141
  · exact source_chunk_142
  · exact source_chunk_143
  · exact source_chunk_144
  · exact source_chunk_145
  · exact source_chunk_146
  · exact source_chunk_147
  · exact source_chunk_148
  · exact source_chunk_149
  · exact source_chunk_150
  · exact source_chunk_151
  · exact source_chunk_152
  · exact source_chunk_153

theorem targets_checked_fast :
    allIndexed (fastTargetCheck 19683 19 23 3 G19 G23 endpointTable) 0 rows = true := by
  apply allIndexed_of_blocks (P := fastTargetCheck 19683 19 23 3 G19 G23 endpointTable)
    (rows := rows) (b := 128) (c := 154) (by decide) (by rw [rows_size]; decide)
  intro i
  fin_cases i
  · exact target_chunk_00
  · exact target_chunk_01
  · exact target_chunk_02
  · exact target_chunk_03
  · exact target_chunk_04
  · exact target_chunk_05
  · exact target_chunk_06
  · exact target_chunk_07
  · exact target_chunk_08
  · exact target_chunk_09
  · exact target_chunk_10
  · exact target_chunk_11
  · exact target_chunk_12
  · exact target_chunk_13
  · exact target_chunk_14
  · exact target_chunk_15
  · exact target_chunk_16
  · exact target_chunk_17
  · exact target_chunk_18
  · exact target_chunk_19
  · exact target_chunk_20
  · exact target_chunk_21
  · exact target_chunk_22
  · exact target_chunk_23
  · exact target_chunk_24
  · exact target_chunk_25
  · exact target_chunk_26
  · exact target_chunk_27
  · exact target_chunk_28
  · exact target_chunk_29
  · exact target_chunk_30
  · exact target_chunk_31
  · exact target_chunk_32
  · exact target_chunk_33
  · exact target_chunk_34
  · exact target_chunk_35
  · exact target_chunk_36
  · exact target_chunk_37
  · exact target_chunk_38
  · exact target_chunk_39
  · exact target_chunk_40
  · exact target_chunk_41
  · exact target_chunk_42
  · exact target_chunk_43
  · exact target_chunk_44
  · exact target_chunk_45
  · exact target_chunk_46
  · exact target_chunk_47
  · exact target_chunk_48
  · exact target_chunk_49
  · exact target_chunk_50
  · exact target_chunk_51
  · exact target_chunk_52
  · exact target_chunk_53
  · exact target_chunk_54
  · exact target_chunk_55
  · exact target_chunk_56
  · exact target_chunk_57
  · exact target_chunk_58
  · exact target_chunk_59
  · exact target_chunk_60
  · exact target_chunk_61
  · exact target_chunk_62
  · exact target_chunk_63
  · exact target_chunk_64
  · exact target_chunk_65
  · exact target_chunk_66
  · exact target_chunk_67
  · exact target_chunk_68
  · exact target_chunk_69
  · exact target_chunk_70
  · exact target_chunk_71
  · exact target_chunk_72
  · exact target_chunk_73
  · exact target_chunk_74
  · exact target_chunk_75
  · exact target_chunk_76
  · exact target_chunk_77
  · exact target_chunk_78
  · exact target_chunk_79
  · exact target_chunk_80
  · exact target_chunk_81
  · exact target_chunk_82
  · exact target_chunk_83
  · exact target_chunk_84
  · exact target_chunk_85
  · exact target_chunk_86
  · exact target_chunk_87
  · exact target_chunk_88
  · exact target_chunk_89
  · exact target_chunk_90
  · exact target_chunk_91
  · exact target_chunk_92
  · exact target_chunk_93
  · exact target_chunk_94
  · exact target_chunk_95
  · exact target_chunk_96
  · exact target_chunk_97
  · exact target_chunk_98
  · exact target_chunk_99
  · exact target_chunk_100
  · exact target_chunk_101
  · exact target_chunk_102
  · exact target_chunk_103
  · exact target_chunk_104
  · exact target_chunk_105
  · exact target_chunk_106
  · exact target_chunk_107
  · exact target_chunk_108
  · exact target_chunk_109
  · exact target_chunk_110
  · exact target_chunk_111
  · exact target_chunk_112
  · exact target_chunk_113
  · exact target_chunk_114
  · exact target_chunk_115
  · exact target_chunk_116
  · exact target_chunk_117
  · exact target_chunk_118
  · exact target_chunk_119
  · exact target_chunk_120
  · exact target_chunk_121
  · exact target_chunk_122
  · exact target_chunk_123
  · exact target_chunk_124
  · exact target_chunk_125
  · exact target_chunk_126
  · exact target_chunk_127
  · exact target_chunk_128
  · exact target_chunk_129
  · exact target_chunk_130
  · exact target_chunk_131
  · exact target_chunk_132
  · exact target_chunk_133
  · exact target_chunk_134
  · exact target_chunk_135
  · exact target_chunk_136
  · exact target_chunk_137
  · exact target_chunk_138
  · exact target_chunk_139
  · exact target_chunk_140
  · exact target_chunk_141
  · exact target_chunk_142
  · exact target_chunk_143
  · exact target_chunk_144
  · exact target_chunk_145
  · exact target_chunk_146
  · exact target_chunk_147
  · exact target_chunk_148
  · exact target_chunk_149
  · exact target_chunk_150
  · exact target_chunk_151
  · exact target_chunk_152
  · exact target_chunk_153

theorem targets_checked :
    allIndexed (targetCheck rows.length 19 23 3 G19 G23 endpointTable) 0 rows = true := by
  simpa only [fastTargetCheck_eq, rows_size] using targets_checked_fast

end

end Sarkozy.OddOrder437
