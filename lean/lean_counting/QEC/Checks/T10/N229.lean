import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 112430232..112921192 of seam certificate T10. -/
theorem near229 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 112430232 112921193 = true := by
  native_decide

end QECChecks.T10
