import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 1016879..1080433 of seam certificate T8. -/
theorem near16 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 1016879 1080434 = true := by
  native_decide

end QECChecks.T8
