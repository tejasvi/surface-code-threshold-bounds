import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 24548085..25039046 of seam certificate T10. -/
theorem near50 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 24548085 25039047 = true := by
  native_decide

end QECChecks.T10
