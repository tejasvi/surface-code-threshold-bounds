import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1416 = true := by
  decide +kernel

theorem tot1416 : totK PA10K2 A10K2.t1416 = [0, 0, 0, 257913039921, 1485730205716, 2060721651005, 723959967775, 45545545079, 0, 0] := by
  decide +kernel

theorem rows1417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1417 = true := by
  decide +kernel

theorem tot1417 : totK PA10K2 A10K2.t1417 = [0, 0, 0, 0, 645436858845, 2124868210197, 1568689886613, 241080017594, 6354482628, 0] := by
  decide +kernel

theorem rows1418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1418 = true := by
  decide +kernel

theorem tot1418 : totK PA10K2 A10K2.t1418 = [0, 0, 0, 0, 484275783687, 1788215266942, 1874751559126, 518414009289, 31756067336, 0] := by
  decide +kernel

theorem rows1419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1419 = true := by
  decide +kernel

theorem tot1419 : totK PA10K2 A10K2.t1419 = [0, 0, 0, 0, 697573028563, 2051451884969, 1535470096582, 304782958095, 12657047711, 0] := by
  decide +kernel

end QECKChecks.A10K2
