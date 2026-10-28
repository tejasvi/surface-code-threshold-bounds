import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_33_5_5_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 0] [] = true := by
  decide +kernel

theorem dfs_33_5_5_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 1] [] = true := by
  decide +kernel

theorem dfs_33_5_5_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 2] [] = true := by
  decide +kernel

theorem dfs_33_5_5_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 3] [] = true := by
  decide +kernel

theorem dfs_33_5_5_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 4] [] = true := by
  decide +kernel

theorem dfs_33_5_5_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 5] [] = true := by
  decide +kernel

theorem dfs_33_5_5_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 6] [] = true := by
  decide +kernel

theorem dfs_33_5_5_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 33) [5, 5, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
