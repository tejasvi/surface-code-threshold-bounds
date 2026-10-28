import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 77080988..77571949 of seam certificate T10. -/
theorem near157 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 77080988 77571950 = true := by
  native_decide

end QECChecks.T10
