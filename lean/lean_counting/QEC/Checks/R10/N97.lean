import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 48587965..49088871 of augmented certificate R10. -/
theorem near97 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 48587965 49088872 = true := by
  native_decide

end QECChecks.R10
