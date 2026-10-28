import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3495522..3559076 of seam certificate T8. -/
theorem near55 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3495522 3559077 = true := by
  native_decide

end QECChecks.T8
