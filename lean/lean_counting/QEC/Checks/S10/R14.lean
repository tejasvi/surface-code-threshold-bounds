import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 866073..927935 of certificate S10. -/
theorem rows14 : rowsOKS PS10 keysS10 HsS10 866073 927936 = true := by
  native_decide

end QECChecks.S10
