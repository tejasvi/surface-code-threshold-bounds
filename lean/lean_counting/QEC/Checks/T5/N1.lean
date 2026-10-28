import QECCountComp.Data.T5

namespace QECChecks.T5

open QECComp QECComp.Data

/-- Rows of the near states 12196..24391 of seam certificate T5. -/
theorem near1 : nearRowsOK PT5 nkT5 nGT5 bkT5 bHT5 12196 24392 = true := by
  native_decide

end QECChecks.T5
