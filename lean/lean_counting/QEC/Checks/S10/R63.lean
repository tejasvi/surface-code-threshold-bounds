import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3897332..3959193 of certificate S10. -/
theorem rows63 : rowsOKS PS10 keysS10 HsS10 3897332 3959194 = true := by
  native_decide

end QECChecks.S10
