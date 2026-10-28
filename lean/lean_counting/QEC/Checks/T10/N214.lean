import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 105065806..105556767 of seam certificate T10. -/
theorem near214 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 105065806 105556768 = true := by
  native_decide

end QECChecks.T10
