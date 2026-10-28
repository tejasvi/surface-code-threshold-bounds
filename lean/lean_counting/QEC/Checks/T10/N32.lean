import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 15710774..16201735 of seam certificate T10. -/
theorem near32 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 15710774 16201736 = true := by
  native_decide

end QECChecks.T10
