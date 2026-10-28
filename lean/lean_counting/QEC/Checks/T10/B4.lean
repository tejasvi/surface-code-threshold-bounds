import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states 1965491..2456862 of seam certificate T10. -/
theorem bulk4 : bulkRowsOK PT10 nkT10 nGT10 bkT10 bHT10 1965491 2456863 = true := by
  native_decide

end QECChecks.T10
