import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The bulk rows (head height bigH) of the bulk states 485385..970769 of augmented certificate R10. -/
theorem b1 : bulkRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 485385 970770 = true := by
  native_decide

end QECChecks.R10
