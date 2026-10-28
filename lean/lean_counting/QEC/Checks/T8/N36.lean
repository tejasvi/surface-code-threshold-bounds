import QECCountComp.Data.T8

namespace QECChecks.T8

open QECComp QECComp.Data

/-- Rows of the near states 2287978..2351532 of seam certificate T8. -/
theorem near36 : nearRowsOK PT8 nkT8 nGT8 bkT8 bHT8 2287978 2351533 = true := by
  native_decide

end QECChecks.T8
