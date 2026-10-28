import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows401 : rowsOKK PKA8 tKA8 137401 137744 = true := by
  decide +kernel

end QECKChecks.KA8
