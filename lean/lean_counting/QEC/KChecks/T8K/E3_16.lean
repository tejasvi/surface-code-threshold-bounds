import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_3_2_0_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 0] [] = true := by
  decide +kernel

theorem dfs_3_2_0_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 1] [] = true := by
  decide +kernel

theorem dfs_3_2_0_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 2] [] = true := by
  decide +kernel

theorem dfs_3_2_0_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 3] [] = true := by
  decide +kernel

theorem dfs_3_2_0_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 4] [] = true := by
  decide +kernel

theorem dfs_3_2_0_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 5] [] = true := by
  decide +kernel

theorem dfs_3_2_0_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 6] [] = true := by
  decide +kernel

theorem dfs_3_2_0_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 3) [2, 0, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
