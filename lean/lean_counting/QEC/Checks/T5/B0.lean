import QECCountComp.Data.T5

namespace QECChecks.T5

open QECComp QECComp.Data

/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states 0..1219 of seam certificate T5. -/
theorem bulk0 : bulkRowsOK PT5 nkT5 nGT5 bkT5 bHT5 0 1220 = true := by
  native_decide

end QECChecks.T5
