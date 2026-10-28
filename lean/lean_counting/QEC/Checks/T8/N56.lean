import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3559077..3622631 of seam certificate T8. -/
theorem near56 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3559077 3622632 = true := by
  native_decide

end QECChecks.T8
