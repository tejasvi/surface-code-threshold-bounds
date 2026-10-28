import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- The interface rows (head height HC) of the bulk states 2912311..3397695 of augmented certificate R10. -/
theorem i6 : ifRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 2912311 3397696 = true := by
  native_decide

end QECChecks.R10
