import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 141887934..142378895 of seam certificate T10. -/
theorem near289 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 141887934 142378896 = true := by
  native_decide

end QECChecks.T10
