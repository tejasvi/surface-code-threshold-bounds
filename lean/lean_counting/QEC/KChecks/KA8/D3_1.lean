import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem dfs3_1 : dfsTop2K PKA8 tKA8 3 1 = true := by
  decide +kernel

end QECKChecks.KA8
