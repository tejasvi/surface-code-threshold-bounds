import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1484698..1546559 of certificate S10. -/
theorem rows24 : rowsOKS PS10 keysS10 HsS10 1484698 1546560 = true := by
  native_decide

end QECChecks.S10
