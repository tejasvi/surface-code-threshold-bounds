import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 128631968..129122929 of seam certificate T10. -/
theorem near262 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 128631968 129122930 = true := by
  native_decide

end QECChecks.T10
