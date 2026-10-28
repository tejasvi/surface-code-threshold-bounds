import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 38295013..38785974 of seam certificate T10. -/
theorem near78 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 38295013 38785975 = true := by
  native_decide

end QECChecks.T10
