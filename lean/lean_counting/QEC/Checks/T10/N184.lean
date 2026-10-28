import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 90336955..90827915 of seam certificate T10. -/
theorem near184 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 90336955 90827916 = true := by
  native_decide

end QECChecks.T10
