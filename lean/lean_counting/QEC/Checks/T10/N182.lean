import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 89355031..89845992 of seam certificate T10. -/
theorem near182 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 89355031 89845993 = true := by
  native_decide

end QECChecks.T10
