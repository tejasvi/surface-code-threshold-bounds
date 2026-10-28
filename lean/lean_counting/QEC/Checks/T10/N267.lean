import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 131086777..131577737 of seam certificate T10. -/
theorem near267 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 131086777 131577738 = true := by
  native_decide

end QECChecks.T10
