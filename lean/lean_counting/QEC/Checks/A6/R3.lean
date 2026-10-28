import QECCountComp.Data.A6

namespace QECChecks.A6

open QECComp QECComp.Data

/-- Rows of the states 4693..6257 of certificate A6. -/
theorem rows3 : rowsOK PA6 keysA6 HsA6 4693 6258 = true := by
  native_decide

end QECChecks.A6
