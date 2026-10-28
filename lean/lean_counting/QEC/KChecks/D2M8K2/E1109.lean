import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_7_8_5_0 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 0] [] = true := by
  decide +kernel

theorem dfs_7_8_5_1 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 1] [] = true := by
  decide +kernel

theorem dfs_7_8_5_2 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 2] [] = true := by
  decide +kernel

theorem dfs_7_8_5_3 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 3] [] = true := by
  decide +kernel

theorem dfs_7_8_5_4 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 4] [] = true := by
  decide +kernel

theorem dfs_7_8_5_5 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 5] [] = true := by
  decide +kernel

theorem dfs_7_8_5_6 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 6] [] = true := by
  decide +kernel

theorem dfs_7_8_5_7 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 7] [] = true := by
  decide +kernel

theorem dfs_7_8_5_8 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 8] [] = true := by
  decide +kernel

theorem dfs_7_8_5_9 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 9] [] = true := by
  decide +kernel

theorem dfs_7_8_5_10 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 10] [] = true := by
  decide +kernel

theorem dfs_7_8_5_11 : dfsPreK PD2M8K2 tD2M8K2 [7, 8, 5, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
