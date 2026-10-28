import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4830176..4893730 of seam certificate T8. -/
theorem near76 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4830176 4893731 = true := by
  native_decide

end QECChecks.T8
