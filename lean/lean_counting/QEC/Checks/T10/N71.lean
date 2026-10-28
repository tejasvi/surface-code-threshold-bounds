import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 34858281..35349242 of seam certificate T10. -/
theorem near71 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 34858281 35349243 = true := by
  native_decide

end QECChecks.T10
