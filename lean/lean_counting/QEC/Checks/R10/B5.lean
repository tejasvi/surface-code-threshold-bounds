import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The bulk rows (head height bigH) of the bulk states 2426926..2912310 of augmented certificate R10. -/
theorem b5 : bulkRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 2426926 2912311 = true := by
  native_decide

end QECChecks.R10
