import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 147288513..147779474 of seam certificate T10. -/
theorem near300 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 147288513 147779475 = true := by
  native_decide

end QECChecks.T10
