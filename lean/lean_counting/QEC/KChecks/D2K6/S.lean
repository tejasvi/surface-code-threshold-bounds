import QECCountComp.KData.D2K6

namespace QECKChecks.D2K6

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem size : tD2K6.toList.length = 72294 := by
  decide +kernel

theorem start : startOKK PD2K6 tD2K6 = true := by
  decide +kernel

end QECKChecks.D2K6
