import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 989798..1051660 of certificate S10. -/
theorem rows16 : rowsOKS PS10 keysS10 HsS10 989798 1051661 = true := by
  native_decide

end QECChecks.S10
