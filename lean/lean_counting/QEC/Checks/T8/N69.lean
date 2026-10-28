import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 4385291..4448845 of seam certificate T8. -/
theorem near69 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 4385291 4448846 = true := by
  native_decide

end QECChecks.T8
