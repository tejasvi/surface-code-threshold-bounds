import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 804211..866072 of certificate S10. -/
theorem rows13 : rowsOKS PS10 keysS10 HsS10 804211 866073 = true := by
  native_decide

end QECChecks.S10
