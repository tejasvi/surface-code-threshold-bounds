import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 85427337..85918298 of seam certificate T10. -/
theorem near174 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 85427337 85918299 = true := by
  native_decide

end QECChecks.T10
