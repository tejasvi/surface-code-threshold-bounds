import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2227047..2288908 of certificate S10. -/
theorem rows36 : rowsOKS PS10 keysS10 HsS10 2227047 2288909 = true := by
  native_decide

end QECChecks.S10
