import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows308 : rowsOKK PKA8 tKA8 105535 105878 = true := by
  decide +kernel

end QECKChecks.KA8
