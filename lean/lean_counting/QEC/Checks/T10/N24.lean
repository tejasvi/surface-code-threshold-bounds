import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 11783081..12274041 of seam certificate T10. -/
theorem near24 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 11783081 12274042 = true := by
  native_decide

end QECChecks.T10
