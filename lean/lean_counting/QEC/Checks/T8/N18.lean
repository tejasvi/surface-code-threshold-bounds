import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1143989..1207543 of seam certificate T8. -/
theorem near18 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1143989 1207544 = true := by
  native_decide

end QECChecks.T8
