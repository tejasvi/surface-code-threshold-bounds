import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The bulk rows (head height bigH) of the bulk states 970770..1456154 of augmented certificate R10. -/
theorem b2 : bulkRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 970770 1456155 = true := by
  native_decide

end QECChecks.R10
