import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows259 : rowsOKK PKA8 tKA8 88745 89088 = true := by
  decide +kernel

end QECKChecks.KA8
