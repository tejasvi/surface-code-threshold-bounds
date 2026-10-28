import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 62352137..62843098 of seam certificate T10. -/
theorem near127 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 62352137 62843099 = true := by
  native_decide

end QECChecks.T10
