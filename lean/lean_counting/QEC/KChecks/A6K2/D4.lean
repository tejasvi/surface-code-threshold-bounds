import QECCountComp.KData.A6K2

namespace QECKChecks.A6K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_4_0 : dfsPreK PA6K2 tA6K2 [4, 0] [] = true := by
  decide +kernel

theorem dfs_4_1 : dfsPreK PA6K2 tA6K2 [4, 1] [] = true := by
  decide +kernel

theorem dfs_4_2 : dfsPreK PA6K2 tA6K2 [4, 2] [] = true := by
  decide +kernel

theorem dfs_4_3 : dfsPreK PA6K2 tA6K2 [4, 3] [] = true := by
  decide +kernel

theorem dfs_4_4 : dfsPreK PA6K2 tA6K2 [4, 4] [] = true := by
  decide +kernel

theorem dfs_4_5 : dfsPreK PA6K2 tA6K2 [4, 5] [] = true := by
  decide +kernel

theorem dfs_4_6 : dfsPreK PA6K2 tA6K2 [4, 6] [] = true := by
  decide +kernel

theorem dfs_4_7 : dfsPreK PA6K2 tA6K2 [4, 7] [] = true := by
  decide +kernel

end QECKChecks.A6K2
