import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1334653..1398207 of seam certificate T8. -/
theorem near21 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1334653 1398208 = true := by
  native_decide

end QECChecks.T8
