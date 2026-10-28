import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3304857..3368411 of seam certificate T8. -/
theorem near52 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3304857 3368412 = true := by
  native_decide

end QECChecks.T8
