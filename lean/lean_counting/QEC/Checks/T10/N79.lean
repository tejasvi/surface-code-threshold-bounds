import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 38785975..39276936 of seam certificate T10. -/
theorem near79 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 38785975 39276937 = true := by
  native_decide

end QECChecks.T10
