import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 69626053..70126959 of augmented certificate R10. -/
theorem near139 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 69626053 70126960 = true := by
  native_decide

end QECChecks.R10
