import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1113523..1175384 of certificate S10. -/
theorem rows18 : rowsOKS PS10 keysS10 HsS10 1113523 1175385 = true := by
  native_decide

end QECChecks.S10
