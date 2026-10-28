import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 31557132..32058038 of augmented certificate R10. -/
theorem near63 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 31557132 32058039 = true := by
  native_decide

end QECChecks.R10
