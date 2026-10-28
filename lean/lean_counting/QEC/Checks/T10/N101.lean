import QECCountComp.Data.T10

namespace QECChecks.T10

open QECComp QECComp.Data

/-- Rows of the near states 49587132..50078093 of seam certificate T10. -/
theorem near101 : nearRowsOK PT10 nkT10 nGT10 bkT10 bHT10 49587132 50078094 = true := by
  native_decide

end QECChecks.T10
