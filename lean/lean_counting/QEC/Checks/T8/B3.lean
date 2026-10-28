import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows (offsets bigO, HC, -HC - 1) of the bulk states 59626..79501 of seam certificate T8. -/
theorem bulk3 : bulkRowsOK PT8 nkT8 nGT8 bkT8 bHT8 59626 79502 = true := by
  native_decide

end QECChecks.T8
