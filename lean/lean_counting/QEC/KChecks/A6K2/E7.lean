import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_7_0 : dfsPreK PA6K2 tA6K2 [7, 0] [] = true := by
  decide +kernel

theorem dfs_7_1 : dfsPreK PA6K2 tA6K2 [7, 1] [] = true := by
  decide +kernel

theorem dfs_7_2 : dfsPreK PA6K2 tA6K2 [7, 2] [] = true := by
  decide +kernel

theorem dfs_7_3 : dfsPreK PA6K2 tA6K2 [7, 3] [] = true := by
  decide +kernel

theorem dfs_7_4 : dfsPreK PA6K2 tA6K2 [7, 4] [] = true := by
  decide +kernel

theorem dfs_7_5 : dfsPreK PA6K2 tA6K2 [7, 5] [] = true := by
  decide +kernel

theorem dfs_7_6 : dfsPreK PA6K2 tA6K2 [7, 6] [] = true := by
  decide +kernel

theorem dfs_7_7 : dfsPreK PA6K2 tA6K2 [7, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
