import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 55600661..56101567 of augmented certificate R10. -/
theorem near111 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 55600661 56101568 = true := by
  native_decide

end QECChecks.R10
