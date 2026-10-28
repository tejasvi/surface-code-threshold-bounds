import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 699104..762658 of seam certificate T8. -/
theorem near11 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 699104 762659 = true := by
  native_decide

end QECChecks.T8
