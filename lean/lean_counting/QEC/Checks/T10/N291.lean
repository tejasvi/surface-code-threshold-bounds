import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 142869858..143360819 of seam certificate T10. -/
theorem near291 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 142869858 143360820 = true := by
  native_decide

end QECChecks.T10
