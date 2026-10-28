import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 123724..185586 of certificate S10. -/
theorem rows2 : rowsOKS PS10 keysS10 HsS10 123724 185587 = true := by
  native_decide

end QECChecks.S10
