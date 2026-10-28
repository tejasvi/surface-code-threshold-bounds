import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 81008682..81499643 of seam certificate T10. -/
theorem near165 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 81008682 81499644 = true := by
  native_decide

end QECChecks.T10
