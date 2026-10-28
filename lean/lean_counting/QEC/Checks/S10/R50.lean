import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3093120..3154982 of certificate S10. -/
theorem rows50 : rowsOKS PS10 keysS10 HsS10 3093120 3154983 = true := by
  native_decide

end QECChecks.S10
