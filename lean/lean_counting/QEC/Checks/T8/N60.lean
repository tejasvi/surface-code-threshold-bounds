import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3813297..3876850 of seam certificate T8. -/
theorem near60 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3813297 3876851 = true := by
  native_decide

end QECChecks.T8
