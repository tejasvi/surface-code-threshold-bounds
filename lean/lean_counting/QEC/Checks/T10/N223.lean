import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 109484461..109975422 of seam certificate T10. -/
theorem near223 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 109484461 109975423 = true := by
  native_decide

end QECChecks.T10
