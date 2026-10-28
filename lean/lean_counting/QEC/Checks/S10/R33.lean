import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 2041459..2103321 of certificate S10. -/
theorem rows33 : rowsOKS PS10 keysS10 HsS10 2041459 2103322 = true := by
  native_decide

end QECChecks.S10
