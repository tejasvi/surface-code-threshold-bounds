import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 20129430..20620390 of seam certificate T10. -/
theorem near41 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 20129430 20620391 = true := by
  native_decide

end QECChecks.T10
