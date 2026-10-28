import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3154983..3216844 of certificate S10. -/
theorem rows51 : rowsOKS PS10 keysS10 HsS10 3154983 3216845 = true := by
  native_decide

end QECChecks.S10
