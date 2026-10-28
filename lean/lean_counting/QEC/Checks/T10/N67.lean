import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 32894434..33385395 of seam certificate T10. -/
theorem near67 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 32894434 33385396 = true := by
  native_decide

end QECChecks.T10
