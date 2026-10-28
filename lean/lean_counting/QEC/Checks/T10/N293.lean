import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 143851781..144342742 of seam certificate T10. -/
theorem near293 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 143851781 144342743 = true := by
  native_decide

end QECChecks.T10
