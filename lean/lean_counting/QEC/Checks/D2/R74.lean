import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4057029..4111853 of certificate D2. -/
theorem rows74 : rowsOK PD2 keysD2 HsD2 4057029 4111854 = true := by
  native_decide

end QECChecks.D2
