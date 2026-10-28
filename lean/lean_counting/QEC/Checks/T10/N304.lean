import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 149252360..149743321 of seam certificate T10. -/
theorem near304 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 149252360 149743322 = true := by
  native_decide

end QECChecks.T10
