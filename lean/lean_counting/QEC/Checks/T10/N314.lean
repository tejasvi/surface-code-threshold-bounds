import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 154161977..154652938 of seam certificate T10. -/
theorem near314 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 154161977 154652939 = true := by
  native_decide

end QECChecks.T10
