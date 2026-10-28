import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3711745..3773606 of certificate S10. -/
theorem rows60 : rowsOKS PS10 keysS10 HsS10 3711745 3773607 = true := by
  native_decide

end QECChecks.S10
