import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 156616786..157107747 of seam certificate T10. -/
theorem near319 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 156616786 157107748 = true := by
  native_decide

end QECChecks.T10
