import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The sizes of augmented certificate R10. -/
theorem sizes : nkR10.size = 82148725 ∧ nGR10.size = 82148725 ∧ bkR10.size = 3883082 ∧ bHR10.size = 3883082 := by
  native_decide

/-- The start bounds (every first-vertex height), augmented certificate R10. -/
theorem start : startOKA PR10 nkR10 nGR10 bkR10 bHR10 = true := by
  native_decide

end QECChecks.R10
