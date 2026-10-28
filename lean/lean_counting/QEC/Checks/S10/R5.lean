import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 309312..371173 of certificate S10. -/
theorem rows5 : rowsOKS PS10 keysS10 HsS10 309312 371174 = true := by
  native_decide

end QECChecks.S10
