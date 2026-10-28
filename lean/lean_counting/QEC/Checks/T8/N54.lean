import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3431967..3495521 of seam certificate T8. -/
theorem near54 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3431967 3495522 = true := by
  native_decide

end QECChecks.T8
