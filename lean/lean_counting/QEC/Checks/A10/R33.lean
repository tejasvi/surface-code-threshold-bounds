import QECCountComp.Data.A10

namespace QECChecks.A10

open QECComp QECComp.Data

/-- Rows of the states 2002214..2062886 of certificate A10. -/
theorem rows33 : rowsOK PA10 keysA10 HsA10 2002214 2062887 = true := by
  native_decide

end QECChecks.A10
