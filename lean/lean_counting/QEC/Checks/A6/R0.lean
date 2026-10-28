import QECCountComp.Data.A6

namespace QECChecks.A6

open QECComp QECComp.Data

/-- Rows of the states 0..1563 of certificate A6. -/
theorem rows0 : rowsOK PA6 keysA6 HsA6 0 1564 = true := by
  native_decide

end QECChecks.A6
