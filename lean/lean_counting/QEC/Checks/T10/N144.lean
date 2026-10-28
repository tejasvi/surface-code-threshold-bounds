import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 70698486..71189447 of seam certificate T10. -/
theorem near144 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 70698486 71189448 = true := by
  native_decide

end QECChecks.T10
