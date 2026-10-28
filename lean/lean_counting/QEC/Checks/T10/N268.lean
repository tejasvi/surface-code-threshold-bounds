import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 131577738..132068699 of seam certificate T10. -/
theorem near268 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 131577738 132068700 = true := by
  native_decide

end QECChecks.T10
