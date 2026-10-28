import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 39276937..39767897 of seam certificate T10. -/
theorem near80 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 39276937 39767898 = true := by
  native_decide

end QECChecks.T10
