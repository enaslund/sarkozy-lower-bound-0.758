import Sarkozy.OneOddTarget
import Sarkozy.Odd437Certificate

/-!
# The unconditional full exponent

All nine component certificates are proved, including both reconstructed odd
witnesses and their numerical moments. No finite-certificate hypothesis remains.
-/

namespace Sarkozy

/-- Square-difference-free sets of size N^(0.75806746-o(1)). -/
theorem record_exponent : LowerBoundExponent targetExponent := by
  obtain ⟨C,a,w,hC,hgeom,horder,hmoment⟩ := OddOrder437.interval_certificate
  exact target_exponent_of_one_odd_interval_certificate C a w hC hgeom horder hmoment

end Sarkozy
