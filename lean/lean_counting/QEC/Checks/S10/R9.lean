import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 556761..618623 of certificate S10. -/
theorem rows9 : rowsOKS PS10 keysS10 HsS10 556761 618624 = true := by
  native_decide

end QECChecks.S10
