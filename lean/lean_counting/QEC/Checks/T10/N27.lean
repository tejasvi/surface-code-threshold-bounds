import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 13255966..13746926 of seam certificate T10. -/
theorem near27 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 13255966 13746927 = true := by
  native_decide

end QECChecks.T10
