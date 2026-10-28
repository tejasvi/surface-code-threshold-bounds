import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 55099754..55600660 of augmented certificate R10. -/
theorem near110 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 55099754 55600661 = true := by
  native_decide

end QECChecks.R10
