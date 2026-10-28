import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 143360820..143851780 of seam certificate T10. -/
theorem near292 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 143360820 143851781 = true := by
  native_decide

end QECChecks.T10
