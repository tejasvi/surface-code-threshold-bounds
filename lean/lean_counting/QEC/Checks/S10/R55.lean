import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3402432..3464294 of certificate S10. -/
theorem rows55 : rowsOKS PS10 keysS10 HsS10 3402432 3464295 = true := by
  native_decide

end QECChecks.S10
