import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_0_8_1_0 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 0] [] = true := by
  decide +kernel

theorem dfs_0_8_1_1 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 1] [] = true := by
  decide +kernel

theorem dfs_0_8_1_2 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 2] [] = true := by
  decide +kernel

theorem dfs_0_8_1_3 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 3] [] = true := by
  decide +kernel

theorem dfs_0_8_1_4 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 4] [] = true := by
  decide +kernel

theorem dfs_0_8_1_5 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 5] [] = true := by
  decide +kernel

theorem dfs_0_8_1_6 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 6] [] = true := by
  decide +kernel

theorem dfs_0_8_1_7 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 7] [] = true := by
  decide +kernel

theorem dfs_0_8_1_8 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 8] [] = true := by
  decide +kernel

theorem dfs_0_8_1_9 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 9] [] = true := by
  decide +kernel

theorem dfs_0_8_1_10 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 10] [] = true := by
  decide +kernel

theorem dfs_0_8_1_11 : dfsPreK PD2M8K2 tD2M8K2 [0, 8, 1, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
