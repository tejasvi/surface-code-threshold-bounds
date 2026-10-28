import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 18656545..19147505 of seam certificate T10. -/
theorem near38 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 18656545 19147506 = true := by
  native_decide

end QECChecks.T10
