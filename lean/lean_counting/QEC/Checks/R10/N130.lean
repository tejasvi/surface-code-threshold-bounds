import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 65117891..65618797 of augmented certificate R10. -/
theorem near130 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 65117891 65618798 = true := by
  native_decide

end QECChecks.R10
