import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2907533..2969395 of certificate S10. -/
theorem rows47 : rowsOKS PS10 keysS10 HsS10 2907533 2969396 = true := by
  native_decide

end QECChecks.S10
