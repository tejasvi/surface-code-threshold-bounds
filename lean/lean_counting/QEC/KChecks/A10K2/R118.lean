import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t472 = true := by
  decide +kernel

theorem tot472 : totK PA10K2 A10K2.t472 = [460770283454, 1631014449482, 1829051880547, 772431424775, 89425356090, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t473 = true := by
  decide +kernel

theorem tot473 : totK PA10K2 A10K2.t473 = [285708781362, 1475073473939, 2097875727933, 796428618361, 60088777011, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t474 = true := by
  decide +kernel

theorem tot474 : totK PA10K2 A10K2.t474 = [299193715415, 1138044445860, 1839081360279, 1225994079985, 221156802292, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t475 = true := by
  decide +kernel

theorem tot475 : totK PA10K2 A10K2.t475 = [296697742459, 1591157913788, 2284585662522, 911865026584, 77509523968, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
