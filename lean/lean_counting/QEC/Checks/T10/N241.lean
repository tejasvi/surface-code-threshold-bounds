import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 118321772..118812733 of seam certificate T10. -/
theorem near241 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 118321772 118812734 = true := by
  native_decide

end QECChecks.T10
