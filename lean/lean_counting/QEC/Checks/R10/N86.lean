import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 43077989..43578895 of augmented certificate R10. -/
theorem near86 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 43077989 43578896 = true := by
  native_decide

end QECChecks.R10
