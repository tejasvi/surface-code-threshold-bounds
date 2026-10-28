import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 111939270..112430231 of seam certificate T10. -/
theorem near228 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 111939270 112430232 = true := by
  native_decide

end QECChecks.T10
