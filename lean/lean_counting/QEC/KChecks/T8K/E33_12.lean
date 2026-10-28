import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_33_1_4_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 0] [] = true := by
  decide +kernel

theorem dfs_33_1_4_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 1] [] = true := by
  decide +kernel

theorem dfs_33_1_4_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 2] [] = true := by
  decide +kernel

theorem dfs_33_1_4_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 3] [] = true := by
  decide +kernel

theorem dfs_33_1_4_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 4] [] = true := by
  decide +kernel

theorem dfs_33_1_4_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 5] [] = true := by
  decide +kernel

theorem dfs_33_1_4_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 6] [] = true := by
  decide +kernel

theorem dfs_33_1_4_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [1, 4, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
