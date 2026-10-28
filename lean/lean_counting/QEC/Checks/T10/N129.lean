import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 63334060..63825021 of seam certificate T10. -/
theorem near129 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 63334060 63825022 = true := by
  native_decide

end QECChecks.T10
