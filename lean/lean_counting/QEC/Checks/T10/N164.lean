import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 80517720..81008681 of seam certificate T10. -/
theorem near164 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 80517720 81008682 = true := by
  native_decide

end QECChecks.T10
