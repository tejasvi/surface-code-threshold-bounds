import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 145324666..145815627 of seam certificate T10. -/
theorem near296 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 145324666 145815628 = true := by
  native_decide

end QECChecks.T10
