import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem size : tKA8.toList.length = 157618 := by
  decide +kernel

theorem start : startOKK PKA8 tKA8 = true := by
  decide +kernel

end QECKChecks.KA8
