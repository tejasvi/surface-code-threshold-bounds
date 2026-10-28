import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1608422..1670284 of certificate S10. -/
theorem rows26 : rowsOKS PS10 keysS10 HsS10 1608422 1670285 = true := by
  native_decide

end QECChecks.S10
