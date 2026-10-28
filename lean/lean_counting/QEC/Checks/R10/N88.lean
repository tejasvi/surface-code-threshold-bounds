import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 44079803..44580709 of augmented certificate R10. -/
theorem near88 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 44079803 44580710 = true := by
  native_decide

end QECChecks.R10
