import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 138451202..138942163 of seam certificate T10. -/
theorem near282 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 138451202 138942164 = true := by
  native_decide

end QECChecks.T10
