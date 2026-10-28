import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 635549..699103 of seam certificate T8. -/
theorem near10 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 635549 699104 = true := by
  native_decide

end QECChecks.T8
