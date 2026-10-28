import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2796417..2859971 of seam certificate T8. -/
theorem near44 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2796417 2859972 = true := by
  native_decide

end QECChecks.T8
