import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 433036..494898 of certificate S10. -/
theorem rows7 : rowsOKS PS10 keysS10 HsS10 433036 494899 = true := by
  native_decide

end QECChecks.S10
