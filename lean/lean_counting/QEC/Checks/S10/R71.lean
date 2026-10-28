import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 4392231..4454093 of certificate S10. -/
theorem rows71 : rowsOKS PS10 keysS10 HsS10 4392231 4454094 = true := by
  native_decide

end QECChecks.S10
