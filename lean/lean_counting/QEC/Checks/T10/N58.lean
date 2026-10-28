import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 28475779..28966740 of seam certificate T10. -/
theorem near58 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 28475779 28966741 = true := by
  native_decide

end QECChecks.T10
