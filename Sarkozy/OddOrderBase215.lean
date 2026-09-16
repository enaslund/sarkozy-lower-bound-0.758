import Sarkozy.OddOrderData215
import Sarkozy.OddOrderFast

/-!
# Basic data checks shared by the 215 order-verification chunks

The source and target mask checks are split into sequentially imported chunks
to bound peak kernel evaluation state and preserve completed work in the cache.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Sarkozy.OddOrder215

open OddOrder

noncomputable def G5 : List ℤ → ℕ := fastPrefixLookup 5 table5

noncomputable def G43 : List ℤ → ℕ := fastPrefixLookup 43 table43

def denominator : ℕ := 100000000000000

theorem rows_size : rows.length = 4913 := by decide +kernel

theorem rows_valid : rows.all (fun r => OddData.valid 125 79507 denominator r.1) = true := by
  decide +kernel

theorem endpoints_sorted : (rows.map entryEnd).IsChain (· ≤ ·) := by
  decide +kernel

end Sarkozy.OddOrder215
