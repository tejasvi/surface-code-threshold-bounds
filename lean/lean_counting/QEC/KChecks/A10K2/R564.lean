import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2256 = true := by
  decide +kernel

theorem tot2256 : totK PA10K2 A10K2.t2256 = [0, 466136094182, 1715160732279, 1893058853056, 602140572231, 37254374173, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2257 = true := by
  decide +kernel

theorem tot2257 : totK PA10K2 A10K2.t2257 = [0, 108061833447, 1180810563610, 2253664159388, 1006468254563, 71750890109, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2258 = true := by
  decide +kernel

theorem tot2258 : totK PA10K2 A10K2.t2258 = [0, 475019784619, 1559312389391, 1797982806602, 908578346593, 169287513335, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2259 = true := by
  decide +kernel

theorem tot2259 : totK PA10K2 A10K2.t2259 = [0, 310203719009, 1506439159936, 2174701541529, 919203864830, 77181132210, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
