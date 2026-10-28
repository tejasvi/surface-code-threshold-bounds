import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 24043529..24544435 of augmented certificate R10. -/
theorem near48 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 24043529 24544436 = true := by
  native_decide

end QECChecks.R10
