import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3464295..3526156 of certificate S10. -/
theorem rows56 : rowsOKS PS10 keysS10 HsS10 3464295 3526157 = true := by
  native_decide

end QECChecks.S10
