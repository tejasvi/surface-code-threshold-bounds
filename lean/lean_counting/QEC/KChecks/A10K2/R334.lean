import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1336 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1336 = true := by
  decide +kernel

theorem tot1336 : totK PA10K2 A10K2.t1336 = [0, 0, 105088995274, 811660162267, 2131368772564, 1736075568307, 308127608928, 8047840951, 0, 0] := by
  decide +kernel

theorem rows1337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1337 = true := by
  decide +kernel

theorem tot1337 : totK PA10K2 A10K2.t1337 = [0, 0, 566925367473, 1985782772290, 2024553238030, 540057235105, 25436917169, 0, 0, 0] := by
  decide +kernel

theorem rows1338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1338 = true := by
  decide +kernel

theorem tot1338 : totK PA10K2 A10K2.t1338 = [0, 0, 121146523123, 1069579298926, 2231192700774, 1480240267705, 246841182743, 6279851884, 0, 0] := by
  decide +kernel

theorem rows1339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1339 = true := by
  decide +kernel

theorem tot1339 : totK PA10K2 A10K2.t1339 = [0, 0, 0, 465816348806, 1878273941763, 2123411819094, 596197222317, 18770739859, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
