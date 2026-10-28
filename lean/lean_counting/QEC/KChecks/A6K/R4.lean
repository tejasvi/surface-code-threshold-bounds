import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem rows4 : rowsOKK PA6K tA6K 391 488 = true := by
  decide +kernel

end QECKChecks.A6K
