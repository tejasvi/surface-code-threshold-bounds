import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_2_8_6_0 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 0] [] = true := by
  decide +kernel

theorem dfs_2_8_6_1 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 1] [] = true := by
  decide +kernel

theorem dfs_2_8_6_2 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 2] [] = true := by
  decide +kernel

theorem dfs_2_8_6_3 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 3] [] = true := by
  decide +kernel

theorem dfs_2_8_6_4 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 4] [] = true := by
  decide +kernel

theorem dfs_2_8_6_5 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 5] [] = true := by
  decide +kernel

theorem dfs_2_8_6_6 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 6] [] = true := by
  decide +kernel

theorem dfs_2_8_6_7 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 7] [] = true := by
  decide +kernel

theorem dfs_2_8_6_8 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 8] [] = true := by
  decide +kernel

theorem dfs_2_8_6_9 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 9] [] = true := by
  decide +kernel

theorem dfs_2_8_6_10 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 10] [] = true := by
  decide +kernel

theorem dfs_2_8_6_11 : dfsPreK PD2M8K2 tD2M8K2 [2, 8, 6, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
