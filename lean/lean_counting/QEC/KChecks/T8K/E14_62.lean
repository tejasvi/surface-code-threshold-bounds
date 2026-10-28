import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_14_7_6_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 0] [] = true := by
  decide +kernel

theorem dfs_14_7_6_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 1] [] = true := by
  decide +kernel

theorem dfs_14_7_6_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 2] [] = true := by
  decide +kernel

theorem dfs_14_7_6_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 3] [] = true := by
  decide +kernel

theorem dfs_14_7_6_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 4] [] = true := by
  decide +kernel

theorem dfs_14_7_6_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 5] [] = true := by
  decide +kernel

theorem dfs_14_7_6_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 6] [] = true := by
  decide +kernel

theorem dfs_14_7_6_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 14) [7, 6, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
