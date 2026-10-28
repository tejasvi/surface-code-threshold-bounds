import QECCountComp.KData.D2K6

namespace QECKChecks.D2K6

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem rows74 : rowsOKK PD2K6 tD2K6 20897 21179 = true := by
  decide +kernel

end QECKChecks.D2K6
