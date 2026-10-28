import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 78062912..78553873 of seam certificate T10. -/
theorem near159 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 78062912 78553874 = true := by
  native_decide

end QECChecks.T10
