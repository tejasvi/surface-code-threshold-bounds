import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 49096171..49587131 of seam certificate T10. -/
theorem near100 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 49096171 49587132 = true := by
  native_decide

end QECChecks.T10
