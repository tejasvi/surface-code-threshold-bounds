import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_6_0 : dfsPreK PA6K2 tA6K2 [6, 0] [] = true := by
  decide +kernel

theorem dfs_6_1 : dfsPreK PA6K2 tA6K2 [6, 1] [] = true := by
  decide +kernel

theorem dfs_6_2 : dfsPreK PA6K2 tA6K2 [6, 2] [] = true := by
  decide +kernel

theorem dfs_6_3 : dfsPreK PA6K2 tA6K2 [6, 3] [] = true := by
  decide +kernel

theorem dfs_6_4 : dfsPreK PA6K2 tA6K2 [6, 4] [] = true := by
  decide +kernel

theorem dfs_6_5 : dfsPreK PA6K2 tA6K2 [6, 5] [] = true := by
  decide +kernel

theorem dfs_6_6 : dfsPreK PA6K2 tA6K2 [6, 6] [] = true := by
  decide +kernel

theorem dfs_6_7 : dfsPreK PA6K2 tA6K2 [6, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
