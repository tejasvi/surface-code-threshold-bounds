import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 27048970..27549876 of augmented certificate R10. -/
theorem near54 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 27048970 27549877 = true := by
  native_decide

end QECChecks.R10
