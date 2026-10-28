import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3368412..3431966 of seam certificate T8. -/
theorem near53 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3368412 3431967 = true := by
  native_decide

end QECChecks.T8
