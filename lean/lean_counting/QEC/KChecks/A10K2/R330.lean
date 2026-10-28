import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1320 = true := by
  decide +kernel

theorem tot1320 : totK PA10K2 A10K2.t1320 = [0, 0, 0, 582288507160, 1997004430618, 1901074751925, 398215087269, 12224107035, 0, 0] := by
  decide +kernel

theorem rows1321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1321 = true := by
  decide +kernel

theorem tot1321 : totK PA10K2 A10K2.t1321 = [0, 0, 315335427872, 1082029331688, 1538170013955, 1344439056223, 527238028223, 48886019071, 0, 0] := by
  decide +kernel

theorem rows1322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1322 = true := by
  decide +kernel

theorem tot1322 : totK PA10K2 A10K2.t1322 = [0, 0, 528848366904, 1918532767067, 1957240378780, 516275824257, 16452360677, 0, 0, 0] := by
  decide +kernel

theorem rows1323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1323 = true := by
  decide +kernel

theorem tot1323 : totK PA10K2 A10K2.t1323 = [0, 0, 0, 620630355807, 2001743238482, 1648187523729, 395836961056, 25333254304, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
