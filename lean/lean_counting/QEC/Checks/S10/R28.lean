import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 1732147..1794009 of certificate S10. -/
theorem rows28 : rowsOKS PS10 keysS10 HsS10 1732147 1794010 = true := by
  native_decide

end QECChecks.S10
