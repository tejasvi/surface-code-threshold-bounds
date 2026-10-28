import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1237248..1299109 of certificate S10. -/
theorem rows20 : rowsOKS PS10 keysS10 HsS10 1237248 1299110 = true := by
  native_decide

end QECChecks.S10
