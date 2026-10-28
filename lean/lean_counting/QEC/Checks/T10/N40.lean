import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 19638468..20129429 of seam certificate T10. -/
theorem near40 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 19638468 20129430 = true := by
  native_decide

end QECChecks.T10
