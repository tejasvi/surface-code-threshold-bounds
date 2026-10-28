import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 146306590..146797551 of seam certificate T10. -/
theorem near298 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 146306590 146797552 = true := by
  native_decide

end QECChecks.T10
