import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 52532903..53023863 of seam certificate T10. -/
theorem near107 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 52532903 53023864 = true := by
  native_decide

end QECChecks.T10
