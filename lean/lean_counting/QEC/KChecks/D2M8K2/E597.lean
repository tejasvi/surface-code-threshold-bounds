import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_4_1_9_0 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 0] [] = true := by
  decide +kernel

theorem dfs_4_1_9_1 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 1] [] = true := by
  decide +kernel

theorem dfs_4_1_9_2 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 2] [] = true := by
  decide +kernel

theorem dfs_4_1_9_3 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 3] [] = true := by
  decide +kernel

theorem dfs_4_1_9_4 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 4] [] = true := by
  decide +kernel

theorem dfs_4_1_9_5 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 5] [] = true := by
  decide +kernel

theorem dfs_4_1_9_6 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 6] [] = true := by
  decide +kernel

theorem dfs_4_1_9_7 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 7] [] = true := by
  decide +kernel

theorem dfs_4_1_9_8 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 8] [] = true := by
  decide +kernel

theorem dfs_4_1_9_9 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 9] [] = true := by
  decide +kernel

theorem dfs_4_1_9_10 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 10] [] = true := by
  decide +kernel

theorem dfs_4_1_9_11 : dfsPreK PD2M8K2 tD2M8K2 [4, 1, 9, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
