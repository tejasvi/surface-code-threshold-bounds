import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 89845993..90336954 of seam certificate T10. -/
theorem near183 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 89845993 90336955 = true := by
  native_decide

end QECChecks.T10
