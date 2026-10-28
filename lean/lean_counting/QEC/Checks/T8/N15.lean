import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 953324..1016878 of seam certificate T8. -/
theorem near15 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 953324 1016879 = true := by
  native_decide

end QECChecks.T8
