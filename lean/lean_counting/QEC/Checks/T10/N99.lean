import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 48605209..49096170 of seam certificate T10. -/
theorem near99 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 48605209 49096171 = true := by
  native_decide

end QECChecks.T10
