import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 42076176..42577082 of augmented certificate R10. -/
theorem near84 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 42076176 42577083 = true := by
  native_decide

end QECChecks.R10
