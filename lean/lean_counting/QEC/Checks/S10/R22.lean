import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1360973..1422834 of certificate S10. -/
theorem rows22 : rowsOKS PS10 keysS10 HsS10 1360973 1422835 = true := by
  native_decide

end QECChecks.S10
