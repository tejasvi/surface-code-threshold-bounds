import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2608945..2669617 of certificate A10. -/
theorem rows43 : rowsOK PA10 keysA10 HsA10 2608945 2669618 = true := by
  native_decide

end QECChecks.A10
