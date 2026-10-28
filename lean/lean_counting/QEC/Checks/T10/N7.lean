import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 3436731..3927692 of seam certificate T10. -/
theorem near7 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 3436731 3927693 = true := by
  native_decide

end QECChecks.T10
