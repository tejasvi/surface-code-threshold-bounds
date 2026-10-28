import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 4418655..4909616 of seam certificate T10. -/
theorem near9 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 4418655 4909617 = true := by
  native_decide

end QECChecks.T10
