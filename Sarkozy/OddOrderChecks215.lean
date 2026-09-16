import Sarkozy.OddOrderChunks215.Chunk38
import Sarkozy.OddOrderChunkLemma

/-!
# Every row of the actual 215 order certificate is checked

The generic block-concatenation theorem combines the independently checked
source and target chunks without reevaluating their certificate computations.
-/

namespace Sarkozy.OddOrder215

open OddOrder

theorem sources_checked : allIndexed (sourceCheck 5 43 3 G5 G43 endpointTable) 0 rows = true := by
  apply allIndexed_of_blocks (P := sourceCheck 5 43 3 G5 G43 endpointTable)
    (rows := rows) (b := 128) (c := 39) (by decide) (by rw [rows_size]; decide)
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

theorem targets_checked_fast :
    allIndexed (fastTargetCheck 4913 5 43 3 G5 G43 endpointTable) 0 rows = true := by
  apply allIndexed_of_blocks (P := fastTargetCheck 4913 5 43 3 G5 G43 endpointTable)
    (rows := rows) (b := 128) (c := 39) (by decide) (by rw [rows_size]; decide)
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

theorem targets_checked :
    allIndexed (targetCheck rows.length 5 43 3 G5 G43 endpointTable) 0 rows = true := by
  simpa only [fastTargetCheck_eq, rows_size] using targets_checked_fast

end Sarkozy.OddOrder215
