import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3622632..3686186 of seam certificate T8. -/
theorem near57 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3622632 3686187 = true := by
  native_decide

end QECChecks.T8
