import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3050637..3114191 of seam certificate T8. -/
theorem near48 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3050637 3114192 = true := by
  native_decide

end QECChecks.T8
