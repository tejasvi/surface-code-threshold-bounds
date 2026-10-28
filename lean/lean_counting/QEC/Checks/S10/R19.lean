import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1175385..1237247 of certificate S10. -/
theorem rows19 : rowsOKS PS10 keysS10 HsS10 1175385 1237248 = true := by
  native_decide

end QECChecks.S10
