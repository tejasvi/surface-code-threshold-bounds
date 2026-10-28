import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 45582524..46083430 of augmented certificate R10. -/
theorem near91 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 45582524 46083431 = true := by
  native_decide

end QECChecks.R10
