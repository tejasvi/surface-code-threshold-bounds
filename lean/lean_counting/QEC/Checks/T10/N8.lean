import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 3927693..4418654 of seam certificate T10. -/
theorem near8 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 3927693 4418655 = true := by
  native_decide

end QECChecks.T10
