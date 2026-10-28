import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 98683304..99174264 of seam certificate T10. -/
theorem near201 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 98683304 99174265 = true := by
  native_decide

end QECChecks.T10
