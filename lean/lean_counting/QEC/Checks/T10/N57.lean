import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 27984817..28475778 of seam certificate T10. -/
theorem near57 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 27984817 28475779 = true := by
  native_decide

end QECChecks.T10
