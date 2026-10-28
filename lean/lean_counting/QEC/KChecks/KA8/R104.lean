import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows104 : rowsOKK PKA8 tKA8 35635 35978 = true := by
  decide +kernel

end QECKChecks.KA8
