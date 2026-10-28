import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_2_0 : dfsPreK PA6K2 tA6K2 [2, 0] [] = true := by
  decide +kernel

theorem dfs_2_1 : dfsPreK PA6K2 tA6K2 [2, 1] [] = true := by
  decide +kernel

theorem dfs_2_2 : dfsPreK PA6K2 tA6K2 [2, 2] [] = true := by
  decide +kernel

theorem dfs_2_3 : dfsPreK PA6K2 tA6K2 [2, 3] [] = true := by
  decide +kernel

theorem dfs_2_4 : dfsPreK PA6K2 tA6K2 [2, 4] [] = true := by
  decide +kernel

theorem dfs_2_5 : dfsPreK PA6K2 tA6K2 [2, 5] [] = true := by
  decide +kernel

theorem dfs_2_6 : dfsPreK PA6K2 tA6K2 [2, 6] [] = true := by
  decide +kernel

theorem dfs_2_7 : dfsPreK PA6K2 tA6K2 [2, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
