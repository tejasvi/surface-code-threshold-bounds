import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1906648..1970202 of seam certificate T8. -/
theorem near30 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1906648 1970203 = true := by
  native_decide

end QECChecks.T8
