import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 95737533..96228494 of seam certificate T10. -/
theorem near195 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 95737533 96228495 = true := by
  native_decide

end QECChecks.T10
