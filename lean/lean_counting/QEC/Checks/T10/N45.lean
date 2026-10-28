import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 22093277..22584237 of seam certificate T10. -/
theorem near45 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 22093277 22584238 = true := by
  native_decide

end QECChecks.T10
