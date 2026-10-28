import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1917734..1979596 of certificate S10. -/
theorem rows31 : rowsOKS PS10 keysS10 HsS10 1917734 1979597 = true := by
  native_decide

end QECChecks.S10
