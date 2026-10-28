import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 78141470..78642375 of augmented certificate R10. -/
theorem near156 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 78141470 78642376 = true := by
  native_decide

end QECChecks.R10
