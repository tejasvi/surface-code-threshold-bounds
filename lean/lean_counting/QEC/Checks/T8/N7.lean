import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 444884..508438 of seam certificate T8. -/
theorem near7 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 444884 508439 = true := by
  native_decide

end QECChecks.T8
