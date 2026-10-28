import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 105556768..106047728 of seam certificate T10. -/
theorem near215 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 105556768 106047729 = true := by
  native_decide

end QECChecks.T10
