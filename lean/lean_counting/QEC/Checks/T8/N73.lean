import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4639511..4703065 of seam certificate T8. -/
theorem near73 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4639511 4703066 = true := by
  native_decide

end QECChecks.T8
