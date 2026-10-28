import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 53023864..53514825 of seam certificate T10. -/
theorem near108 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 53023864 53514826 = true := by
  native_decide

end QECChecks.T10
