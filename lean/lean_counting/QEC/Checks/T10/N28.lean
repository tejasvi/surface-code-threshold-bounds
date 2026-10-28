import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 13746927..14237888 of seam certificate T10. -/
theorem near28 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 13746927 14237889 = true := by
  native_decide

end QECChecks.T10
