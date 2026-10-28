import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1432 = true := by
  decide +kernel

theorem tot1432 : totK PA10K2 A10K2.t1432 = [0, 0, 366888563271, 1646982033636, 2012404282881, 637711279243, 38180250037, 0, 0, 0] := by
  decide +kernel

theorem rows1433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1433 = true := by
  decide +kernel

theorem tot1433 : totK PA10K2 A10K2.t1433 = [0, 0, 113553474827, 869257820761, 2035330297704, 1380067507113, 210620501165, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1434 = true := by
  decide +kernel

theorem tot1434 : totK PA10K2 A10K2.t1434 = [0, 0, 472246657175, 1812711601205, 2079884574253, 645185814482, 38229687576, 0, 0, 0] := by
  decide +kernel

theorem rows1435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1435 = true := by
  decide +kernel

theorem tot1435 : totK PA10K2 A10K2.t1435 = [0, 0, 0, 583535283307, 2028743855994, 1983933996296, 431359640491, 12746179907, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
