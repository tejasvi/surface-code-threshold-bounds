import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2923527..2987081 of seam certificate T8. -/
theorem near46 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2923527 2987082 = true := by
  native_decide

end QECChecks.T8
