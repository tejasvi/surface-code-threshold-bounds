import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 129122930..129613891 of seam certificate T10. -/
theorem near263 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 129122930 129613892 = true := by
  native_decide

end QECChecks.T10
