import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 59607916..60108822 of augmented certificate R10. -/
theorem near119 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 59607916 60108823 = true := by
  native_decide

end QECChecks.R10
