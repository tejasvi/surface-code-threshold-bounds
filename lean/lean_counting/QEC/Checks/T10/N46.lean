import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 22584238..23075199 of seam certificate T10. -/
theorem near46 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 22584238 23075200 = true := by
  native_decide

end QECChecks.T10
