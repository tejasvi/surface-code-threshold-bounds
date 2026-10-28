import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 127109..190663 of seam certificate T8. -/
theorem near2 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 127109 190664 = true := by
  native_decide

end QECChecks.T8
