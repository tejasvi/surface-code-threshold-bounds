import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1794010..1855871 of certificate S10. -/
theorem rows29 : rowsOKS PS10 keysS10 HsS10 1794010 1855872 = true := by
  native_decide

end QECChecks.S10
