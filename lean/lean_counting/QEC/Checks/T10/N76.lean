import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 37313090..37804050 of seam certificate T10. -/
theorem near76 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 37313090 37804051 = true := by
  native_decide

end QECChecks.T10
