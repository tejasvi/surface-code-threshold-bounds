import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 77571950..78062911 of seam certificate T10. -/
theorem near158 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 77571950 78062912 = true := by
  native_decide

end QECChecks.T10
