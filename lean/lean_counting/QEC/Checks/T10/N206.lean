import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 101138112..101629073 of seam certificate T10. -/
theorem near206 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 101138112 101629074 = true := by
  native_decide

end QECChecks.T10
