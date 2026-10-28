import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 46641362..47132323 of seam certificate T10. -/
theorem near95 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 46641362 47132324 = true := by
  native_decide

end QECChecks.T10
