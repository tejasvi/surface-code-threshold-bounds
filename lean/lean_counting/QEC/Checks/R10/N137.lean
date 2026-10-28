import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 68624239..69125145 of augmented certificate R10. -/
theorem near137 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 68624239 69125146 = true := by
  native_decide

end QECChecks.R10
