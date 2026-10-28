import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- The number of states of certificate A10. -/
theorem size : keysA10.size = 3883082 := by
  native_decide

/-- The start sum of certificate A10. -/
theorem start : startOK PA10 keysA10 HsA10 = true := by
  native_decide

end QECChecks.A10
