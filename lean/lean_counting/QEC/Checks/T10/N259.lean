import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 127159083..127650044 of seam certificate T10. -/
theorem near259 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 127159083 127650045 = true := by
  native_decide

end QECChecks.T10
