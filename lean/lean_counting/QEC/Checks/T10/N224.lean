import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 109975423..110466384 of seam certificate T10. -/
theorem near224 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 109975423 110466385 = true := by
  native_decide

end QECChecks.T10
