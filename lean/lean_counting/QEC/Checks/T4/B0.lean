import QECCountComp.Data.T4

namespace QECChecks.T4

open QECComp QECComp.Data

/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states 0..239 of seam certificate T4. -/
theorem bulk0 : bulkRowsOK PT4 nkT4 nGT4 bkT4 bHT4 0 240 = true := by
  native_decide

end QECChecks.T4
