import QECCountComp.Data.AH4

namespace QECChecks.AH4

open QECComp QECComp.Data

/-- Rows of the near states 0..2597 of augmented certificate AH4. -/
theorem near0 : nearRowsOKA PAH4 nkAH4 nGAH4 bkAH4 bHAH4 0 2598 = true := by
  native_decide

end QECChecks.AH4
