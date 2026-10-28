import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 927936..989797 of certificate S10. -/
theorem rows15 : rowsOKS PS10 keysS10 HsS10 927936 989798 = true := by
  native_decide

end QECChecks.S10
