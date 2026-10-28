import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3526157..3588019 of certificate S10. -/
theorem rows57 : rowsOKS PS10 keysS10 HsS10 3526157 3588020 = true := by
  native_decide

end QECChecks.S10
