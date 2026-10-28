import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 16692698..17183658 of seam certificate T10. -/
theorem near34 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 16692698 17183659 = true := by
  native_decide

end QECChecks.T10
