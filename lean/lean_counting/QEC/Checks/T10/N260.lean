import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 127650045..128141005 of seam certificate T10. -/
theorem near260 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 127650045 128141006 = true := by
  native_decide

end QECChecks.T10
