import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 73644256..74135217 of seam certificate T10. -/
theorem near150 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 73644256 74135218 = true := by
  native_decide

end QECChecks.T10
