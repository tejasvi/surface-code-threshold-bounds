import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 4082919..4144780 of certificate S10. -/
theorem rows66 : rowsOKS PS10 keysS10 HsS10 4082919 4144781 = true := by
  native_decide

end QECChecks.S10
