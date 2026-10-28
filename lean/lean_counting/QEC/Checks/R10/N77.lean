import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 38569828..39070734 of augmented certificate R10. -/
theorem near77 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 38569828 39070735 = true := by
  native_decide

end QECChecks.R10
