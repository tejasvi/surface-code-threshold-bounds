import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 371174..433035 of certificate S10. -/
theorem rows6 : rowsOKS PS10 keysS10 HsS10 371174 433036 = true := by
  native_decide

end QECChecks.S10
