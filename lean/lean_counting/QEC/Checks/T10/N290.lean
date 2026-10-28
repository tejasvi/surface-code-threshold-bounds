import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 142378896..142869857 of seam certificate T10. -/
theorem near290 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 142378896 142869858 = true := by
  native_decide

end QECChecks.T10
