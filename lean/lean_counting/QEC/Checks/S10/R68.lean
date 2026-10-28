import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 4206644..4268505 of certificate S10. -/
theorem rows68 : rowsOKS PS10 keysS10 HsS10 4206644 4268506 = true := by
  native_decide

end QECChecks.S10
