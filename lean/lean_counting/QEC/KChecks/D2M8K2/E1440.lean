import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_10_0_0_0 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 0] [] = true := by
  decide +kernel

theorem dfs_10_0_0_1 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 1] [] = true := by
  decide +kernel

theorem dfs_10_0_0_2 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 2] [] = true := by
  decide +kernel

theorem dfs_10_0_0_3 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 3] [] = true := by
  decide +kernel

theorem dfs_10_0_0_4 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 4] [] = true := by
  decide +kernel

theorem dfs_10_0_0_5 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 5] [] = true := by
  decide +kernel

theorem dfs_10_0_0_6 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 6] [] = true := by
  decide +kernel

theorem dfs_10_0_0_7 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 7] [] = true := by
  decide +kernel

theorem dfs_10_0_0_8 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 8] [] = true := by
  decide +kernel

theorem dfs_10_0_0_9 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 9] [] = true := by
  decide +kernel

theorem dfs_10_0_0_10 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 10] [] = true := by
  decide +kernel

theorem dfs_10_0_0_11 : dfsPreK PD2M8K2 tD2M8K2 [10, 0, 0, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
