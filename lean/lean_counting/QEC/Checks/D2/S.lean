import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- The number of states of certificate D2. -/
theorem size : keysD2.size = 5263174 := by
  native_decide

/-- The start sum of certificate D2. -/
theorem start : startOK PD2 keysD2 HsD2 = true := by
  native_decide

end QECChecks.D2
