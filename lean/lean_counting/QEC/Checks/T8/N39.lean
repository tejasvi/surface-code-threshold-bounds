import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2478643..2542197 of seam certificate T8. -/
theorem near39 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2478643 2542198 = true := by
  native_decide

end QECChecks.T8
