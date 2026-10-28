import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 34061666..34562572 of augmented certificate R10. -/
theorem near68 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 34061666 34562573 = true := by
  native_decide

end QECChecks.R10
