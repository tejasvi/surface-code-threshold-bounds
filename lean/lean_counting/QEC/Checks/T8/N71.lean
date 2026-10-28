import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4512401..4575955 of seam certificate T8. -/
theorem near71 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4512401 4575956 = true := by
  native_decide

end QECChecks.T8
