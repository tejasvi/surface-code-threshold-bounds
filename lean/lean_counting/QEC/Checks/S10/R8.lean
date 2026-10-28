import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 494899..556760 of certificate S10. -/
theorem rows8 : rowsOKS PS10 keysS10 HsS10 494899 556761 = true := by
  native_decide

end QECChecks.S10
