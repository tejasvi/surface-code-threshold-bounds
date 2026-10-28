import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3835469..3897331 of certificate S10. -/
theorem rows62 : rowsOKS PS10 keysS10 HsS10 3835469 3897332 = true := by
  native_decide

end QECChecks.S10
