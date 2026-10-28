import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 254219..317773 of seam certificate T8. -/
theorem near4 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 254219 317774 = true := by
  native_decide

end QECChecks.T8
