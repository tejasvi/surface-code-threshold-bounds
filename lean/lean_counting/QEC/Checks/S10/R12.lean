import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 742349..804210 of certificate S10. -/
theorem rows12 : rowsOKS PS10 keysS10 HsS10 742349 804211 = true := by
  native_decide

end QECChecks.S10
