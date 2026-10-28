import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2859972..2923526 of seam certificate T8. -/
theorem near45 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2859972 2923527 = true := by
  native_decide

end QECChecks.T8
