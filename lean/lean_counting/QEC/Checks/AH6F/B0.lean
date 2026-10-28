import QECCountComp.Data.AH6F

namespace QECChecks.AH6F

open QECComp QECComp.Data

/-- The bulk rows (head height bigH) of the bulk states 0..6257 of augmented certificate AH6F. -/
theorem b0 : bulkRowsOKA PAH6F nkAH6F nGAH6F bkAH6F bHAH6F 0 6258 = true := by
  native_decide

end QECChecks.AH6F
