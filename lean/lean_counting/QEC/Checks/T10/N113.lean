import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 55478673..55969634 of seam certificate T10. -/
theorem near113 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 55478673 55969635 = true := by
  native_decide

end QECChecks.T10
