import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 61861175..62352136 of seam certificate T10. -/
theorem near126 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 61861175 62352137 = true := by
  native_decide

end QECChecks.T10
