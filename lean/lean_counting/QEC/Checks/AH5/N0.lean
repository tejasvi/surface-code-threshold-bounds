import QECCountComp.Data.AH5

namespace QECChecks.AH5

open QECComp QECComp.Data

/-- Rows of the near states 0..15231 of augmented certificate AH5. -/
theorem near0 : nearRowsOKA PAH5 nkAH5 nGAH5 bkAH5 bHAH5 0 15232 = true := by
  native_decide

end QECChecks.AH5
