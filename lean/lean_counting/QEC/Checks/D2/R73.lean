import QECCountComp.Data.D2

namespace QECChecks.D2

open QECComp QECComp.Data

/-- Rows of the states 4002205..4057028 of certificate D2. -/
theorem rows73 : rowsOK PD2 keysD2 HsD2 4002205 4057029 = true := by
  native_decide

end QECChecks.D2
