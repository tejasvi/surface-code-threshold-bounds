import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 64315984..64806945 of seam certificate T10. -/
theorem near131 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 64315984 64806946 = true := by
  native_decide

end QECChecks.T10
