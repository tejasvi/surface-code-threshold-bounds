import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 41731745..42222706 of seam certificate T10. -/
theorem near85 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 41731745 42222707 = true := by
  native_decide

end QECChecks.T10
