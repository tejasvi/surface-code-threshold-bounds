import QECCountComp.Data.A6

namespace QECChecks.A6

open QECComp QECComp.Data

/-- Rows of the states 1564..3128 of certificate A6. -/
theorem rows1 : rowsOK PA6 keysA6 HsA6 1564 3129 = true := by
  native_decide

end QECChecks.A6
