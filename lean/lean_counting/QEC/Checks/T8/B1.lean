import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states 19875..39750 of seam certificate T8. -/
theorem bulk1 : bulkRowsOK PT8 nkT8 nGT8 bkT8 bHT8 19875 39751 = true := by
  native_decide

end QECChecks.T8
