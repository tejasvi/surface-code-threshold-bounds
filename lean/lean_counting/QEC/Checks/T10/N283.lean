import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 138942164..139433125 of seam certificate T10. -/
theorem near283 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 138942164 139433126 = true := by
  native_decide

end QECChecks.T10
