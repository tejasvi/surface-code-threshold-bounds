import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 10801157..11292118 of seam certificate T10. -/
theorem near22 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 10801157 11292119 = true := by
  native_decide

end QECChecks.T10
