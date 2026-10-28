import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1546560..1608421 of certificate S10. -/
theorem rows25 : rowsOKS PS10 keysS10 HsS10 1546560 1608422 = true := by
  native_decide

end QECChecks.S10
