import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1979597..2041458 of certificate S10. -/
theorem rows32 : rowsOKS PS10 keysS10 HsS10 1979597 2041459 = true := by
  native_decide

end QECChecks.S10
