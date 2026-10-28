import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4703066..4766620 of seam certificate T8. -/
theorem near74 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4703066 4766621 = true := by
  native_decide

end QECChecks.T8
