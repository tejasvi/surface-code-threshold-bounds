import QECCountComp.KData.KA8

namespace QECKChecks.KA8

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem dfs1_6 : dfsTop2K PKA8 tKA8 1 6 = true := by
  decide +kernel

end QECKChecks.KA8
