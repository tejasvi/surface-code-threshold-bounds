import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2542198..2605751 of seam certificate T8. -/
theorem near40 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2542198 2605752 = true := by
  native_decide

end QECChecks.T8
