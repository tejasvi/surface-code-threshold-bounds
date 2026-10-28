import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 24057123..24548084 of seam certificate T10. -/
theorem near49 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 24057123 24548085 = true := by
  native_decide

end QECChecks.T10
