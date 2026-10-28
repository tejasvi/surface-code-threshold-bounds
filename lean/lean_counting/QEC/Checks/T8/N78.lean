import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4957286..5020840 of seam certificate T8. -/
theorem near78 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4957286 5020841 = true := by
  native_decide

end QECChecks.T8
