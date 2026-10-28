import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2288909..2350770 of certificate S10. -/
theorem rows37 : rowsOKS PS10 keysS10 HsS10 2288909 2350771 = true := by
  native_decide

end QECChecks.S10
