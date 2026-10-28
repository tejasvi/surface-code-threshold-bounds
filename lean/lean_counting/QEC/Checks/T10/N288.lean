import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 141396973..141887933 of seam certificate T10. -/
theorem near288 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 141396973 141887934 = true := by
  native_decide

end QECChecks.T10
