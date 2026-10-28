import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 65297907..65788868 of seam certificate T10. -/
theorem near133 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 65297907 65788869 = true := by
  native_decide

end QECChecks.T10
