import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 508439..571993 of seam certificate T8. -/
theorem near8 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 508439 571994 = true := by
  native_decide

end QECChecks.T8
