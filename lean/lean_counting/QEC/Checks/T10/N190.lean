import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 93282725..93773686 of seam certificate T10. -/
theorem near190 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 93282725 93773687 = true := by
  native_decide

end QECChecks.T10
