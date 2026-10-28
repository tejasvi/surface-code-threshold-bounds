import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 82481567..82972528 of seam certificate T10. -/
theorem near168 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 82481567 82972529 = true := by
  native_decide

end QECChecks.T10
