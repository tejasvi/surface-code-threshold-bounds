import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 41240783..41731744 of seam certificate T10. -/
theorem near84 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 41240783 41731745 = true := by
  native_decide

end QECChecks.T10
