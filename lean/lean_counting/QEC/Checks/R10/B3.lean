import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The bulk rows (head height bigH) of the bulk states 1456155..1941540 of augmented certificate R10. -/
theorem b3 : bulkRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 1456155 1941541 = true := by
  native_decide

end QECChecks.R10
