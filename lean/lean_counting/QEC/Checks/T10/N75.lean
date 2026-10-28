import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 36822128..37313089 of seam certificate T10. -/
theorem near75 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 36822128 37313090 = true := by
  native_decide

end QECChecks.T10
