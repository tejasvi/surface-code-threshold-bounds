import QECCountComp.Data.S10

namespace QECChecks.S10

open QECComp QECComp.Data

/-- Rows of the states 3278708..3340569 of certificate S10. -/
theorem rows53 : rowsOKS PS10 keysS10 HsS10 3278708 3340570 = true := by
  native_decide

end QECChecks.S10
