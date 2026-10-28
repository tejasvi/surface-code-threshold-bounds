import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows161 : rowsOKK PKA8 tKA8 55166 55508 = true := by
  decide +kernel

end QECKChecks.KA8
