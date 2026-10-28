import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_2_3_8_0 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 0] [] = true := by
  decide +kernel

theorem dfs_2_3_8_1 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 1] [] = true := by
  decide +kernel

theorem dfs_2_3_8_2 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 2] [] = true := by
  decide +kernel

theorem dfs_2_3_8_3 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 3] [] = true := by
  decide +kernel

theorem dfs_2_3_8_4 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 4] [] = true := by
  decide +kernel

theorem dfs_2_3_8_5 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 5] [] = true := by
  decide +kernel

theorem dfs_2_3_8_6 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 6] [] = true := by
  decide +kernel

theorem dfs_2_3_8_7 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 7] [] = true := by
  decide +kernel

theorem dfs_2_3_8_8 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 8] [] = true := by
  decide +kernel

theorem dfs_2_3_8_9 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 9] [] = true := by
  decide +kernel

theorem dfs_2_3_8_10 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 10] [] = true := by
  decide +kernel

theorem dfs_2_3_8_11 : dfsPreK PD2M8K2 tD2M8K2 [2, 3, 8, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
