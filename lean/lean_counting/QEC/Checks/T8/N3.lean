import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 190664..254218 of seam certificate T8. -/
theorem near3 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 190664 254219 = true := by
  native_decide

end QECChecks.T8
