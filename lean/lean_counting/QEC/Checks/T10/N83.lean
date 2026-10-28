import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 40749822..41240782 of seam certificate T10. -/
theorem near83 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 40749822 41240783 = true := by
  native_decide

end QECChecks.T10
