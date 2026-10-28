import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows14 : rowsOKK PKA8 tKA8 4797 5139 = true := by
  decide +kernel

end QECKChecks.KA8
