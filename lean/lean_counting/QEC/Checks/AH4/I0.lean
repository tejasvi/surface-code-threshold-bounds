import QECCountComp.Data.AH4

namespace QECChecks.AH4

open QECComp QECComp.Data

/-- The interface rows (head height HC) of the bulk states 0..239 of augmented certificate AH4. -/
theorem i0 : ifRowsOKA PAH4 nkAH4 nGAH4 bkAH4 bHAH4 0 240 = true := by
  native_decide

end QECChecks.AH4
