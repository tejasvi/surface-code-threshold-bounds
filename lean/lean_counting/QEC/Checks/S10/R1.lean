import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 61862..123723 of certificate S10. -/
theorem rows1 : rowsOKS PS10 keysS10 HsS10 61862 123724 = true := by
  native_decide

end QECChecks.S10
