import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 93773687..94264647 of seam certificate T10. -/
theorem near191 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 93773687 94264648 = true := by
  native_decide

end QECChecks.T10
