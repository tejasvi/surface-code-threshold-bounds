import QECCountComp.Data.AH6F

namespace QECChecks.AH6F

open QECComp QECComp.Data

/-- Rows of the near states 0..44489 of augmented certificate AH6F. -/
theorem near0 : nearRowsOKA PAH6F nkAH6F nGAH6F bkAH6F bHAH6F 0 44490 = true := by
  native_decide

end QECChecks.AH6F
