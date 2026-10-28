import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4111854..4166678 of certificate D2. -/
theorem rows75 : rowsOK PD2 keysD2 HsD2 4111854 4166679 = true := by
  native_decide

end QECChecks.D2
