import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows256 : rowsOKK PKA8 tKA8 87717 88060 = true := by
  decide +kernel

end QECKChecks.KA8
