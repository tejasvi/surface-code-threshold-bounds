import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 115376002..115866963 of seam certificate T10. -/
theorem near235 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 115376002 115866964 = true := by
  native_decide

end QECChecks.T10
