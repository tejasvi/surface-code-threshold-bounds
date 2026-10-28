import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states 0..19874 of seam certificate T8. -/
theorem bulk0 : bulkRowsOK PT8 nkT8 nGT8 bkT8 bHT8 0 19875 = true := by
  native_decide

end QECChecks.T8
