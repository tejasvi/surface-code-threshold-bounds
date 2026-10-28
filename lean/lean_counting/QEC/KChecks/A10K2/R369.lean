import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1476 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1476 = true := by
  decide +kernel

theorem tot1476 : totK PA10K2 A10K2.t1476 = [0, 0, 0, 240802378194, 1140414479160, 1941999078672, 1184832030544, 184326589725, 5460492893, 0] := by
  decide +kernel

theorem rows1477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1477 = true := by
  decide +kernel

theorem tot1477 : totK PA10K2 A10K2.t1477 = [0, 0, 0, 343532581041, 1644573733557, 2121697568510, 543936145850, 23826273484, 0, 0] := by
  decide +kernel

theorem rows1478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1478 = true := by
  decide +kernel

theorem tot1478 : totK PA10K2 A10K2.t1478 = [0, 0, 0, 271305974298, 1210647157426, 1931935781671, 1031467621371, 147916450509, 6034215561, 0] := by
  decide +kernel

theorem rows1479 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1479 = true := by
  decide +kernel

theorem tot1479 : totK PA10K2 A10K2.t1479 = [0, 0, 0, 546425824623, 1891326455975, 1756085995605, 389187523444, 16735867423, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
