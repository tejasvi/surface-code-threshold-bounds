import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The interface rows (head height HC) of the bulk states 0..485384 of augmented certificate R10. -/
theorem i0 : ifRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 0 485385 = true := by
  native_decide

end QECChecks.R10
