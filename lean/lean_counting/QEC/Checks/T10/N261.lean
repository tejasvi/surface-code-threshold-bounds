import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 128141006..128631967 of seam certificate T10. -/
theorem near261 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 128141006 128631968 = true := by
  native_decide

end QECChecks.T10
