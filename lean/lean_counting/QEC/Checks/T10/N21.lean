import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 10310195..10801156 of seam certificate T10. -/
theorem near21 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 10310195 10801157 = true := by
  native_decide

end QECChecks.T10
