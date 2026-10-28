import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2350771..2412633 of certificate S10. -/
theorem rows38 : rowsOKS PS10 keysS10 HsS10 2350771 2412634 = true := by
  native_decide

end QECChecks.S10
