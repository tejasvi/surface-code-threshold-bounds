import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 103101959..103592920 of seam certificate T10. -/
theorem near210 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 103101959 103592921 = true := by
  native_decide

end QECChecks.T10
