import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1271099..1334652 of seam certificate T8. -/
theorem near20 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1271099 1334653 = true := by
  native_decide

end QECChecks.T8
