import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1525318..1588872 of seam certificate T8. -/
theorem near24 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1525318 1588873 = true := by
  native_decide

end QECChecks.T8
