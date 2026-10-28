import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_0_0 : dfsPreK PA6K2 tA6K2 [0, 0] [] = true := by
  decide +kernel

theorem dfs_0_1 : dfsPreK PA6K2 tA6K2 [0, 1] [] = true := by
  decide +kernel

theorem dfs_0_2 : dfsPreK PA6K2 tA6K2 [0, 2] [] = true := by
  decide +kernel

theorem dfs_0_3 : dfsPreK PA6K2 tA6K2 [0, 3] [] = true := by
  decide +kernel

theorem dfs_0_4 : dfsPreK PA6K2 tA6K2 [0, 4] [] = true := by
  decide +kernel

theorem dfs_0_5 : dfsPreK PA6K2 tA6K2 [0, 5] [] = true := by
  decide +kernel

theorem dfs_0_6 : dfsPreK PA6K2 tA6K2 [0, 6] [] = true := by
  decide +kernel

theorem dfs_0_7 : dfsPreK PA6K2 tA6K2 [0, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
