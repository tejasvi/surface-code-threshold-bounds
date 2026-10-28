import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 132068700..132559661 of seam certificate T10. -/
theorem near269 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 132068700 132559662 = true := by
  native_decide

end QECChecks.T10
