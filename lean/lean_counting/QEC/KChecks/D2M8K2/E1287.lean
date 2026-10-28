import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_8_11_3_0 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 0] [] = true := by
  decide +kernel

theorem dfs_8_11_3_1 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 1] [] = true := by
  decide +kernel

theorem dfs_8_11_3_2 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 2] [] = true := by
  decide +kernel

theorem dfs_8_11_3_3 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 3] [] = true := by
  decide +kernel

theorem dfs_8_11_3_4 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 4] [] = true := by
  decide +kernel

theorem dfs_8_11_3_5 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 5] [] = true := by
  decide +kernel

theorem dfs_8_11_3_6 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 6] [] = true := by
  decide +kernel

theorem dfs_8_11_3_7 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 7] [] = true := by
  decide +kernel

theorem dfs_8_11_3_8 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 8] [] = true := by
  decide +kernel

theorem dfs_8_11_3_9 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 9] [] = true := by
  decide +kernel

theorem dfs_8_11_3_10 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 10] [] = true := by
  decide +kernel

theorem dfs_8_11_3_11 : dfsPreK PD2M8K2 tD2M8K2 [8, 11, 3, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
