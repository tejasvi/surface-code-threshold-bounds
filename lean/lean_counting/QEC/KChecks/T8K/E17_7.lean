import QECCountComp.KData.T8K

namespace QECKChecks.T8K

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_17_0_7_0 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 0] [] = true := by
  decide +kernel

theorem dfs_17_0_7_1 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 1] [] = true := by
  decide +kernel

theorem dfs_17_0_7_2 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 2] [] = true := by
  decide +kernel

theorem dfs_17_0_7_3 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 3] [] = true := by
  decide +kernel

theorem dfs_17_0_7_4 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 4] [] = true := by
  decide +kernel

theorem dfs_17_0_7_5 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 5] [] = true := by
  decide +kernel

theorem dfs_17_0_7_6 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 6] [] = true := by
  decide +kernel

theorem dfs_17_0_7_7 : dfsPreTK PT8K tNT8K.find tBT8K.find (offT PT8K 17) [0, 7, 7] [] = true := by
  decide +kernel

end QECKChecks.T8K
