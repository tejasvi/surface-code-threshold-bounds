import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t324 = true := by
  decide +kernel

theorem tot324 : totK PA10K2 A10K2.t324 = [0, 41350443019, 531688185324, 1768619015214, 1791773243576, 456200712244, 31333686660, 0, 0, 0] := by
  decide +kernel

theorem rows325 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t325 = true := by
  decide +kernel

theorem tot325 : totK PA10K2 A10K2.t325 = [0, 471228702995, 1718893385607, 1802916607593, 558254441139, 46328355238, 0, 0, 0, 0] := by
  decide +kernel

theorem rows326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t326 = true := by
  decide +kernel

theorem tot326 : totK PA10K2 A10K2.t326 = [0, 308781236982, 1533282292871, 2113982174448, 765975977530, 45913727628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t327 = true := by
  decide +kernel

theorem tot327 : totK PA10K2 A10K2.t327 = [0, 0, 680349980024, 2101208379168, 1530512366993, 262468477233, 6354482628, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
