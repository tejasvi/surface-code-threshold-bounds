import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1843093..1906647 of seam certificate T8. -/
theorem near29 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1843093 1906648 = true := by
  native_decide

end QECChecks.T8
