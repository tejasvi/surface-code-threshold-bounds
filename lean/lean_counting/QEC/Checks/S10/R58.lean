import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3588020..3649881 of certificate S10. -/
theorem rows58 : rowsOKS PS10 keysS10 HsS10 3588020 3649882 = true := by
  native_decide

end QECChecks.S10
