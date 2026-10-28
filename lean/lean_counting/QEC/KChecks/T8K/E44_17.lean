import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_44_2_1_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 0] [] = true := by
  decide +kernel

theorem dfs_44_2_1_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 1] [] = true := by
  decide +kernel

theorem dfs_44_2_1_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 2] [] = true := by
  decide +kernel

theorem dfs_44_2_1_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 3] [] = true := by
  decide +kernel

theorem dfs_44_2_1_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 4] [] = true := by
  decide +kernel

theorem dfs_44_2_1_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 5] [] = true := by
  decide +kernel

theorem dfs_44_2_1_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 6] [] = true := by
  decide +kernel

theorem dfs_44_2_1_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 44) [2, 1, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
