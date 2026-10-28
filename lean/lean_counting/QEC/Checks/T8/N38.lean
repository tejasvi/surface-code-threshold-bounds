import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2415088..2478642 of seam certificate T8. -/
theorem near38 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2415088 2478643 = true := by
  native_decide

end QECChecks.T8
