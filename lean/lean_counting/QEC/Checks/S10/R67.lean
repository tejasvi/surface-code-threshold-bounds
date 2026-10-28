import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 4144781..4206643 of certificate S10. -/
theorem rows67 : rowsOKS PS10 keysS10 HsS10 4144781 4206644 = true := by
  native_decide

end QECChecks.S10
