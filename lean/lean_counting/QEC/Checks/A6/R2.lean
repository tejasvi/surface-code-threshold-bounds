import QECCountComp.Data.A6

namespace QECChecks.A6

open QECComp QECComp.Data

/-- Rows of the states 3129..4692 of certificate A6. -/
theorem rows2 : rowsOK PA6 keysA6 HsA6 3129 4693 = true := by
  native_decide

end QECChecks.A6
