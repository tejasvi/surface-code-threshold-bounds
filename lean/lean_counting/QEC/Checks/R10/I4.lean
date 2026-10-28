import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The interface rows (head height HC) of the bulk states 1941541..2426925 of augmented certificate R10. -/
theorem i4 : ifRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 1941541 2426926 = true := by
  native_decide

end QECChecks.R10
