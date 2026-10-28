import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 3241302..3304856 of seam certificate T8. -/
theorem near51 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 3241302 3304857 = true := by
  native_decide

end QECChecks.T8
