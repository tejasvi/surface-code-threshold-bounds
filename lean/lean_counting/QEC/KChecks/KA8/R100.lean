import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows100 : rowsOKK PKA8 tKA8 34264 34607 = true := by
  decide +kernel

end QECKChecks.KA8
