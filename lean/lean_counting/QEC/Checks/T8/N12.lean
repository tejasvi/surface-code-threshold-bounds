import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 762659..826213 of seam certificate T8. -/
theorem near12 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 762659 826214 = true := by
  native_decide

end QECChecks.T8
