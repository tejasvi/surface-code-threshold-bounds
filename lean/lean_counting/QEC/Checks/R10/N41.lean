import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 20537181..21038087 of augmented certificate R10. -/
theorem near41 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 20537181 21038088 = true := by
  native_decide

end QECChecks.R10
