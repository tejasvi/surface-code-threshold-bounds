import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5540 = true := by
  decide +kernel

theorem tot5540 : totK PA10K2 A10K2.t5540 = [0, 0, 457278332201, 1818298876351, 2057893795658, 593827690282, 23620721234, 0, 0, 0] := by
  decide +kernel

theorem rows5541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5541 = true := by
  decide +kernel

theorem tot5541 : totK PA10K2 A10K2.t5541 = [0, 0, 289014149172, 1443390961548, 2134048719301, 1017314353472, 101534555977, 0, 0, 0] := by
  decide +kernel

theorem rows5542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5542 = true := by
  decide +kernel

theorem tot5542 : totK PA10K2 A10K2.t5542 = [0, 0, 0, 604175647123, 2025035265815, 1901079370426, 379014872942, 12224107035, 0, 0] := by
  decide +kernel

theorem rows5543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5543 = true := by
  decide +kernel

theorem tot5543 : totK PA10K2 A10K2.t5543 = [0, 0, 316661823121, 1159380609827, 1597521499799, 1255541305371, 515105556455, 48886019071, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
