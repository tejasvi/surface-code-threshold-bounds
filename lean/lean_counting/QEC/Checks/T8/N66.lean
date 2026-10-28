import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4194626..4258180 of seam certificate T8. -/
theorem near66 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4194626 4258181 = true := by
  native_decide

end QECChecks.T8
