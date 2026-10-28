import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_1_0 : dfsPreK PA6K2 tA6K2 [1, 0] [] = true := by
  decide +kernel

theorem dfs_1_1 : dfsPreK PA6K2 tA6K2 [1, 1] [] = true := by
  decide +kernel

theorem dfs_1_2 : dfsPreK PA6K2 tA6K2 [1, 2] [] = true := by
  decide +kernel

theorem dfs_1_3 : dfsPreK PA6K2 tA6K2 [1, 3] [] = true := by
  decide +kernel

theorem dfs_1_4 : dfsPreK PA6K2 tA6K2 [1, 4] [] = true := by
  decide +kernel

theorem dfs_1_5 : dfsPreK PA6K2 tA6K2 [1, 5] [] = true := by
  decide +kernel

theorem dfs_1_6 : dfsPreK PA6K2 tA6K2 [1, 6] [] = true := by
  decide +kernel

theorem dfs_1_7 : dfsPreK PA6K2 tA6K2 [1, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
