import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2669307..2732861 of seam certificate T8. -/
theorem near42 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2669307 2732862 = true := by
  native_decide

end QECChecks.T8
