import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 73153295..73644255 of seam certificate T10. -/
theorem near149 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 73153295 73644256 = true := by
  native_decide

end QECChecks.T10
