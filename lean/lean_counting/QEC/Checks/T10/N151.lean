import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 74135218..74626179 of seam certificate T10. -/
theorem near151 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 74135218 74626180 = true := by
  native_decide

end QECChecks.T10
