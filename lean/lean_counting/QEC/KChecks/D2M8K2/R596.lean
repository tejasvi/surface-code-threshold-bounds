import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2384 = true := by
  decide +kernel

theorem tot2384 : totK PD2M8K2 D2M8K2.t2384 = [0, 0, 186379259603, 468287229862, 213877258803, 14625222328, 0, 0] := by
  decide +kernel

theorem rows2385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2385 = true := by
  decide +kernel

theorem tot2385 : totK PD2M8K2 D2M8K2.t2385 = [0, 0, 192956915828, 465542634373, 212093156966, 12361325328, 0, 0] := by
  decide +kernel

theorem rows2386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2386 = true := by
  decide +kernel

theorem tot2386 : totK PD2M8K2 D2M8K2.t2386 = [0, 0, 30258883717, 338333349090, 428497579753, 70234891704, 1239866073, 0] := by
  decide +kernel

theorem rows2387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2387 = true := by
  decide +kernel

theorem tot2387 : totK PD2M8K2 D2M8K2.t2387 = [0, 0, 91138706697, 393963853557, 365977568069, 45375213518, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
