import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_7_9_7_0 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 0] [] = true := by
  decide +kernel

theorem dfs_7_9_7_1 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 1] [] = true := by
  decide +kernel

theorem dfs_7_9_7_2 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 2] [] = true := by
  decide +kernel

theorem dfs_7_9_7_3 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 3] [] = true := by
  decide +kernel

theorem dfs_7_9_7_4 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 4] [] = true := by
  decide +kernel

theorem dfs_7_9_7_5 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 5] [] = true := by
  decide +kernel

theorem dfs_7_9_7_6 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 6] [] = true := by
  decide +kernel

theorem dfs_7_9_7_7 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 7] [] = true := by
  decide +kernel

theorem dfs_7_9_7_8 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 8] [] = true := by
  decide +kernel

theorem dfs_7_9_7_9 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 9] [] = true := by
  decide +kernel

theorem dfs_7_9_7_10 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 10] [] = true := by
  decide +kernel

theorem dfs_7_9_7_11 : dfsPreK PD2M8K2 tD2M8K2 [7, 9, 7, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
