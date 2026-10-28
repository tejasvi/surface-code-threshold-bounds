import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_2_1_2_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 0] [] = true := by
  decide +kernel

theorem dfs_2_1_2_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 1] [] = true := by
  decide +kernel

theorem dfs_2_1_2_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 2] [] = true := by
  decide +kernel

theorem dfs_2_1_2_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 3] [] = true := by
  decide +kernel

theorem dfs_2_1_2_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 4] [] = true := by
  decide +kernel

theorem dfs_2_1_2_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 5] [] = true := by
  decide +kernel

theorem dfs_2_1_2_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 6] [] = true := by
  decide +kernel

theorem dfs_2_1_2_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 2) [1, 2, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
