import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 63554..127108 of seam certificate T8. -/
theorem near1 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 63554 127109 = true := by
  native_decide

end QECChecks.T8
