import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_42_0_3_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 0] [] = true := by
  decide +kernel

theorem dfs_42_0_3_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 1] [] = true := by
  decide +kernel

theorem dfs_42_0_3_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 2] [] = true := by
  decide +kernel

theorem dfs_42_0_3_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 3] [] = true := by
  decide +kernel

theorem dfs_42_0_3_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 4] [] = true := by
  decide +kernel

theorem dfs_42_0_3_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 5] [] = true := by
  decide +kernel

theorem dfs_42_0_3_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 6] [] = true := by
  decide +kernel

theorem dfs_42_0_3_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 42) [0, 3, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
