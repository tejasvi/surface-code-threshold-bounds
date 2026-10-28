import QECCountComp.Data.AH4

namespace QECChecks.AH4

open QECComp QECComp.Data

/-- The sizes of augmented certificate AH4. -/
theorem sizes : nkAH4.size = 2598 ∧ nGAH4.size = 2598 ∧ bkAH4.size = 240 ∧ bHAH4.size = 240 := by
  native_decide

/-- The start bounds (every first-vertex height), augmented certificate AH4. -/
theorem start : startOKA PAH4 nkAH4 nGAH4 bkAH4 bHAH4 = true := by
  native_decide

end QECChecks.AH4
