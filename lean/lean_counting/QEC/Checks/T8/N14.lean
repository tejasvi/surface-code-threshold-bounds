import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 889769..953323 of seam certificate T8. -/
theorem near14 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 889769 953324 = true := by
  native_decide

end QECChecks.T8
