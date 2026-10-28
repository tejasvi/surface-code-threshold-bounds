import QECCountComp.Data.AH5

namespace QECChecks.AH5

open QECComp QECComp.Data

/-- The sizes of augmented certificate AH5. -/
theorem sizes : nkAH5.size = 15232 ∧ nGAH5.size = 15232 ∧ bkAH5.size = 1216 ∧ bHAH5.size = 1216 := by
  native_decide

/-- The start bounds (every first-vertex height), augmented certificate AH5. -/
theorem start : startOKA PAH5 nkAH5 nGAH5 bkAH5 bHAH5 = true := by
  native_decide

end QECChecks.AH5
