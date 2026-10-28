import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3773607..3835468 of certificate S10. -/
theorem rows61 : rowsOKS PS10 keysS10 HsS10 3773607 3835469 = true := by
  native_decide

end QECChecks.S10
