import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 66279831..66770791 of seam certificate T10. -/
theorem near135 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 66279831 66770792 = true := by
  native_decide

end QECChecks.T10
