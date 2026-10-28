import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 17674621..18165582 of seam certificate T10. -/
theorem near36 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 17674621 18165583 = true := by
  native_decide

end QECChecks.T10
