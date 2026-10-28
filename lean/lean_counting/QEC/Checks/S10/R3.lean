import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 185587..247448 of certificate S10. -/
theorem rows3 : rowsOKS PS10 keysS10 HsS10 185587 247449 = true := by
  native_decide

end QECChecks.S10
