import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4003961..4067515 of seam certificate T8. -/
theorem near63 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4003961 4067516 = true := by
  native_decide

end QECChecks.T8
