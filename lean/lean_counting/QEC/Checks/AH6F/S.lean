import QECCountComp.Data.AH6F

namespace QECChecks.AH6F

open QECComp QECComp.Data

/-- The sizes of augmented certificate AH6F. -/
theorem sizes : nkAH6F.size = 88981 ∧ nGAH6F.size = 88981 ∧ bkAH6F.size = 6258 ∧ bHAH6F.size = 6258 := by
  native_decide

/-- The start bounds (every first-vertex height), augmented certificate AH6F. -/
theorem start : startOKA PAH6F nkAH6F nGAH6F bkAH6F bHAH6F = true := by
  native_decide

end QECChecks.AH6F
