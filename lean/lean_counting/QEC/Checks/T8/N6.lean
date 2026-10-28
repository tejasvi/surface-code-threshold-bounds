import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 381329..444883 of seam certificate T8. -/
theorem near6 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 381329 444884 = true := by
  native_decide

end QECChecks.T8
