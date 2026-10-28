import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 20620391..21111352 of seam certificate T10. -/
theorem near42 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 20620391 21111353 = true := by
  native_decide

end QECChecks.T10
