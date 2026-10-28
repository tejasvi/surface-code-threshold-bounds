import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem rows14 : rowsOKK PA6K tA6K 1368 1466 = true := by
  decide +kernel

end QECKChecks.A6K
