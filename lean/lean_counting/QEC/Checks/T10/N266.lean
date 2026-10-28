import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 130595815..131086776 of seam certificate T10. -/
theorem near266 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 130595815 131086777 = true := by
  native_decide

end QECChecks.T10
