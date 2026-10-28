import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 64806946..65297906 of seam certificate T10. -/
theorem near132 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 64806946 65297907 = true := by
  native_decide

end QECChecks.T10
