import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 56951558..57442519 of seam certificate T10. -/
theorem near116 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 56951558 57442520 = true := by
  native_decide

end QECChecks.T10
