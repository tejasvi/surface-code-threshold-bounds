import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 17183659..17674620 of seam certificate T10. -/
theorem near35 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 17183659 17674621 = true := by
  native_decide

end QECChecks.T10
