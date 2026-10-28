import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 119794657..120285618 of seam certificate T10. -/
theorem near244 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 119794657 120285619 = true := by
  native_decide

end QECChecks.T10
