import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 132559662..133050623 of seam certificate T10. -/
theorem near270 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 132559662 133050624 = true := by
  native_decide

end QECChecks.T10
