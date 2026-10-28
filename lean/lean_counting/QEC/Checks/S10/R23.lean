import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1422835..1484697 of certificate S10. -/
theorem rows23 : rowsOKS PS10 keysS10 HsS10 1422835 1484698 = true := by
  native_decide

end QECChecks.S10
