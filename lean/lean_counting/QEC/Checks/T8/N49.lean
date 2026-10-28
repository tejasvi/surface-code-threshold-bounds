import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3114192..3177746 of seam certificate T8. -/
theorem near49 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3114192 3177747 = true := by
  native_decide

end QECChecks.T8
