import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 101629074..102120035 of seam certificate T10. -/
theorem near207 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 101629074 102120036 = true := by
  native_decide

end QECChecks.T10
