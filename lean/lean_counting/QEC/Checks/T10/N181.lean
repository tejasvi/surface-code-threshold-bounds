import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 88864069..89355030 of seam certificate T10. -/
theorem near181 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 88864069 89355031 = true := by
  native_decide

end QECChecks.T10
