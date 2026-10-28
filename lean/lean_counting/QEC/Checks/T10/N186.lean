import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 91318878..91809839 of seam certificate T10. -/
theorem near186 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 91318878 91809840 = true := by
  native_decide

end QECChecks.T10
