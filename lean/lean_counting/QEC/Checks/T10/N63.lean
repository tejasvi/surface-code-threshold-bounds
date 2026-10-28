import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 30930587..31421548 of seam certificate T10. -/
theorem near63 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 30930587 31421549 = true := by
  native_decide

end QECChecks.T10
