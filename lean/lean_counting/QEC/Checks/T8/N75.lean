import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4766621..4830175 of seam certificate T8. -/
theorem near75 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4766621 4830176 = true := by
  native_decide

end QECChecks.T8
