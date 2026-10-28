import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 63114264..63615170 of augmented certificate R10. -/
theorem near126 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 63114264 63615171 = true := by
  native_decide

end QECChecks.R10
