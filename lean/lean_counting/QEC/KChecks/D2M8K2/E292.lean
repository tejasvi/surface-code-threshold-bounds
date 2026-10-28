import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_2_0_4_0 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 0] [] = true := by
  decide +kernel

theorem dfs_2_0_4_1 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 1] [] = true := by
  decide +kernel

theorem dfs_2_0_4_2 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 2] [] = true := by
  decide +kernel

theorem dfs_2_0_4_3 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 3] [] = true := by
  decide +kernel

theorem dfs_2_0_4_4 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 4] [] = true := by
  decide +kernel

theorem dfs_2_0_4_5 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 5] [] = true := by
  decide +kernel

theorem dfs_2_0_4_6 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 6] [] = true := by
  decide +kernel

theorem dfs_2_0_4_7 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 7] [] = true := by
  decide +kernel

theorem dfs_2_0_4_8 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 8] [] = true := by
  decide +kernel

theorem dfs_2_0_4_9 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 9] [] = true := by
  decide +kernel

theorem dfs_2_0_4_10 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 10] [] = true := by
  decide +kernel

theorem dfs_2_0_4_11 : dfsPreK PD2M8K2 tD2M8K2 [2, 0, 4, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
