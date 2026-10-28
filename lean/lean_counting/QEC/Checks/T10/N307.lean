import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 150725245..151216206 of seam certificate T10. -/
theorem near307 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 150725245 151216207 = true := by
  native_decide

end QECChecks.T10
