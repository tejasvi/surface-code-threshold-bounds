import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 317774..381328 of seam certificate T8. -/
theorem near5 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 317774 381329 = true := by
  native_decide

end QECChecks.T8
