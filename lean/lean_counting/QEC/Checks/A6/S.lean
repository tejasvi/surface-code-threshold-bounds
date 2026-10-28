import QECCountComp.Data.A6

namespace QECChecks.A6

open QECComp QECComp.Data

/-- The number of states of certificate A6. -/
theorem size : keysA6.size = 6258 := by
  native_decide

/-- The start sum of certificate A6. -/
theorem start : startOK PA6 keysA6 HsA6 = true := by
  native_decide

end QECChecks.A6
