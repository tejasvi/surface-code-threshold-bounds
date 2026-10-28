import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2605752..2669306 of seam certificate T8. -/
theorem near41 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2605752 2669307 = true := by
  native_decide

end QECChecks.T8
