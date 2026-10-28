import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3649882..3711744 of certificate S10. -/
theorem rows59 : rowsOKS PS10 keysS10 HsS10 3649882 3711745 = true := by
  native_decide

end QECChecks.S10
