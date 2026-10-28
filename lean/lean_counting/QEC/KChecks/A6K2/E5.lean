import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_5_0 : dfsPreK PA6K2 tA6K2 [5, 0] [] = true := by
  decide +kernel

theorem dfs_5_1 : dfsPreK PA6K2 tA6K2 [5, 1] [] = true := by
  decide +kernel

theorem dfs_5_2 : dfsPreK PA6K2 tA6K2 [5, 2] [] = true := by
  decide +kernel

theorem dfs_5_3 : dfsPreK PA6K2 tA6K2 [5, 3] [] = true := by
  decide +kernel

theorem dfs_5_4 : dfsPreK PA6K2 tA6K2 [5, 4] [] = true := by
  decide +kernel

theorem dfs_5_5 : dfsPreK PA6K2 tA6K2 [5, 5] [] = true := by
  decide +kernel

theorem dfs_5_6 : dfsPreK PA6K2 tA6K2 [5, 6] [] = true := by
  decide +kernel

theorem dfs_5_7 : dfsPreK PA6K2 tA6K2 [5, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
