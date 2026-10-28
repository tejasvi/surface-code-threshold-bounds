import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 618624..680485 of certificate S10. -/
theorem rows10 : rowsOKS PS10 keysS10 HsS10 618624 680486 = true := by
  native_decide

end QECChecks.S10
