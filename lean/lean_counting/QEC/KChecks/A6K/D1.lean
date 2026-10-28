import QECCountComp.KData.A6K

namespace QECKChecks.A6K

open QECComp QECComp.KData

set_option maxRecDepth 1000000

theorem dfs1 : dfsTopK PA6K tA6K 1 = true := by
  decide +kernel

end QECKChecks.A6K
