import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states 2948236..3439608 of seam certificate T10. -/
theorem bulk6 : bulkRowsOK PT10 nkT10 nGT10 bkT10 bHT10 2948236 3439609 = true := by
  native_decide

end QECChecks.T10
