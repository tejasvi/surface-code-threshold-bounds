import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 60388290..60879251 of seam certificate T10. -/
theorem near123 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 60388290 60879252 = true := by
  native_decide

end QECChecks.T10
