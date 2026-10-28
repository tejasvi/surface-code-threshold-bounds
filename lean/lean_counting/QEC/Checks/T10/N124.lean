import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 60879252..61370213 of seam certificate T10. -/
theorem near124 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 60879252 61370214 = true := by
  native_decide

end QECChecks.T10
