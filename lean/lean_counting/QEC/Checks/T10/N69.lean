import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 33876358..34367318 of seam certificate T10. -/
theorem near69 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 33876358 34367319 = true := by
  native_decide

end QECChecks.T10
