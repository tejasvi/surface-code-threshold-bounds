import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 27493855..27984816 of seam certificate T10. -/
theorem near56 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 27493855 27984817 = true := by
  native_decide

end QECChecks.T10
