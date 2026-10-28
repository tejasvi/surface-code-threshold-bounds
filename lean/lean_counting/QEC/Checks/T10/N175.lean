import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 85918299..86409260 of seam certificate T10. -/
theorem near175 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 85918299 86409261 = true := by
  native_decide

end QECChecks.T10
