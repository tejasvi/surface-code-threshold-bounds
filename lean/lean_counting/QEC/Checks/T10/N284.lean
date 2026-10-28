import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 139433126..139924087 of seam certificate T10. -/
theorem near284 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 139433126 139924088 = true := by
  native_decide

end QECChecks.T10
