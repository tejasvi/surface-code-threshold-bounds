import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- The number of states of certificate S10. -/
theorem size : keysS10.size = 4454094 := by
  native_decide

/-- The start sum of certificate S10. -/
theorem start : startOK PS10 keysS10 HsS10 = true := by
  native_decide

end QECChecks.S10
