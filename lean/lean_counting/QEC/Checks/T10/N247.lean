import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 121267542..121758503 of seam certificate T10. -/
theorem near247 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 121267542 121758504 = true := by
  native_decide

end QECChecks.T10
