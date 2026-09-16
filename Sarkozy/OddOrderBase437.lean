import Sarkozy.OddOrderData437
import Sarkozy.OddOrderFast

/-!
# Basic data checks shared by the 437 order-verification chunks

The source and target mask checks are split into sequentially imported chunks
to bound peak kernel evaluation state and preserve completed work in the cache.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Sarkozy.OddOrder437

open OddOrder

noncomputable section

def G19 : List ℤ → ℕ := fastPrefixLookup 19 table19

def G23 : List ℤ → ℕ := fastPrefixLookup 23 table23

def denominator : ℕ := 10000000000000000

theorem rows_size : rows.length = 19683 := by decide +kernel

theorem rows_valid : rows.all (fun r => OddData.valid 6859 12167 denominator r.1) = true := by
  decide +kernel

theorem endpoints_sorted : (rows.map entryEnd).IsChain (· ≤ ·) := by
  decide +kernel

end

end Sarkozy.OddOrder437
