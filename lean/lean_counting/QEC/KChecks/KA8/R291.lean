import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows291 : rowsOKK PKA8 tKA8 99710 100053 = true := by
  decide +kernel

end QECKChecks.KA8
