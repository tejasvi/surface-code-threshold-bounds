import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 76590027..77080987 of seam certificate T10. -/
theorem near156 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 76590027 77080988 = true := by
  native_decide

end QECChecks.T10
