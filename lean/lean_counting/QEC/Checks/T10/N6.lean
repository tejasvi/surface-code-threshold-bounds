import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 2945770..3436730 of seam certificate T10. -/
theorem near6 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 2945770 3436731 = true := by
  native_decide

end QECChecks.T10
