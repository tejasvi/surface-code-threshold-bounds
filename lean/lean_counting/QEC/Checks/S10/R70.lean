import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 4330369..4392230 of certificate S10. -/
theorem rows70 : rowsOKS PS10 keysS10 HsS10 4330369 4392231 = true := by
  native_decide

end QECChecks.S10
