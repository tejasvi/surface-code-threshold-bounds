import QECCountComp.Data.AH6F

namespace QECChecks.AH6F

open QECComp QECComp.Data

/-- Rows of the near states 44490..88980 of augmented certificate AH6F. -/
theorem near1 : nearRowsOKA PAH6F nkAH6F nGAH6F bkAH6F bHAH6F 44490 88981 = true := by
  native_decide

end QECChecks.AH6F
