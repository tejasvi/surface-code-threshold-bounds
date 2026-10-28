import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2987082..3050636 of seam certificate T8. -/
theorem near47 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2987082 3050637 = true := by
  native_decide

end QECChecks.T8
