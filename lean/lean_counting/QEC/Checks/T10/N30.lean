import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 14728851..15219812 of seam certificate T10. -/
theorem near30 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 14728851 15219813 = true := by
  native_decide

end QECChecks.T10
