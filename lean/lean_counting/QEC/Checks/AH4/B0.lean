import QECCountComp.Data.AH4

namespace QECChecks.AH4

open QECComp QECComp.Data

/-- The bulk rows (head height bigH) of the bulk states 0..239 of augmented certificate AH4. -/
theorem b0 : bulkRowsOKA PAH4 nkAH4 nGAH4 bkAH4 bHAH4 0 240 = true := by
  native_decide

end QECChecks.AH4
