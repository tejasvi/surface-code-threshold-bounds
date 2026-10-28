import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3686187..3749741 of seam certificate T8. -/
theorem near58 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3686187 3749742 = true := by
  native_decide

end QECChecks.T8
