import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 100647151..101138111 of seam certificate T10. -/
theorem near205 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 100647151 101138112 = true := by
  native_decide

end QECChecks.T10
