import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 7364425..7855386 of seam certificate T10. -/
theorem near15 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 7364425 7855387 = true := by
  native_decide

end QECChecks.T10
