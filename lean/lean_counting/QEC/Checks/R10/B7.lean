import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The bulk rows (head height bigH) of the bulk states 3397696..3883081 of augmented certificate R10. -/
theorem b7 : bulkRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 3397696 3883082 = true := by
  native_decide

end QECChecks.R10
