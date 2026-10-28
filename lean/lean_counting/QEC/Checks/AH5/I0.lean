import QECCountComp.Data.AH5

namespace QECChecks.AH5

open QECComp QECComp.Data

/-- The interface rows (head height HC) of the bulk states 0..1215 of augmented certificate AH5. -/
theorem i0 : ifRowsOKA PAH5 nkAH5 nGAH5 bkAH5 bHAH5 0 1216 = true := by
  native_decide

end QECChecks.AH5
