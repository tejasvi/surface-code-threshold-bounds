import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_3_0 : dfsPreK PA6K2 tA6K2 [3, 0] [] = true := by
  decide +kernel

theorem dfs_3_1 : dfsPreK PA6K2 tA6K2 [3, 1] [] = true := by
  decide +kernel

theorem dfs_3_2 : dfsPreK PA6K2 tA6K2 [3, 2] [] = true := by
  decide +kernel

theorem dfs_3_3 : dfsPreK PA6K2 tA6K2 [3, 3] [] = true := by
  decide +kernel

theorem dfs_3_4 : dfsPreK PA6K2 tA6K2 [3, 4] [] = true := by
  decide +kernel

theorem dfs_3_5 : dfsPreK PA6K2 tA6K2 [3, 5] [] = true := by
  decide +kernel

theorem dfs_3_6 : dfsPreK PA6K2 tA6K2 [3, 6] [] = true := by
  decide +kernel

theorem dfs_3_7 : dfsPreK PA6K2 tA6K2 [3, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
