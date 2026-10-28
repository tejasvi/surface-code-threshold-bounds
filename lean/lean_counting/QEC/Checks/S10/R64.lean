import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3959194..4021056 of certificate S10. -/
theorem rows64 : rowsOKS PS10 keysS10 HsS10 3959194 4021057 = true := by
  native_decide

end QECChecks.S10
