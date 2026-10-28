import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 145815628..146306589 of seam certificate T10. -/
theorem near297 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 145815628 146306590 = true := by
  native_decide

end QECChecks.T10
