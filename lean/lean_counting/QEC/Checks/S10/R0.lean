import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 0..61861 of certificate S10. -/
theorem rows0 : rowsOKS PS10 keysS10 HsS10 0 61862 = true := by
  native_decide

end QECChecks.S10
