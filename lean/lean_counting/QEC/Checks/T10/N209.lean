import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 102610997..103101958 of seam certificate T10. -/
theorem near209 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 102610997 103101959 = true := by
  native_decide

end QECChecks.T10
