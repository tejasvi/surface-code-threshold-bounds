import QECCountComp.Data.R10

namespace QECChecks.R10

open QECComp QECComp.Data

/-- Rows of the near states 32558945..33059851 of augmented certificate R10. -/
theorem near65 : nearRowsOKA PR10 nkR10 nGR10 bkR10 bHR10 32558945 33059852 = true := by
  native_decide

end QECChecks.R10
