import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_3_8_11_0 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 0] [] = true := by
  decide +kernel

theorem dfs_3_8_11_1 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 1] [] = true := by
  decide +kernel

theorem dfs_3_8_11_2 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 2] [] = true := by
  decide +kernel

theorem dfs_3_8_11_3 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 3] [] = true := by
  decide +kernel

theorem dfs_3_8_11_4 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 4] [] = true := by
  decide +kernel

theorem dfs_3_8_11_5 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 5] [] = true := by
  decide +kernel

theorem dfs_3_8_11_6 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 6] [] = true := by
  decide +kernel

theorem dfs_3_8_11_7 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 7] [] = true := by
  decide +kernel

theorem dfs_3_8_11_8 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 8] [] = true := by
  decide +kernel

theorem dfs_3_8_11_9 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 9] [] = true := by
  decide +kernel

theorem dfs_3_8_11_10 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 10] [] = true := by
  decide +kernel

theorem dfs_3_8_11_11 : dfsPreK PD2M8K2 tD2M8K2 [3, 8, 11, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
