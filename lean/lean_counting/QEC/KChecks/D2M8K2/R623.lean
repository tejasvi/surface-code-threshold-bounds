import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2492 = true := by
  decide +kernel

theorem tot2492 : totK PD2M8K2 D2M8K2.t2492 = [90936333741, 353376367700, 354348286970, 72560889913, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows2493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2493 = true := by
  decide +kernel

theorem tot2493 : totK PD2M8K2 D2M8K2.t2493 = [0, 312422481100, 507710163463, 88974907612, 1069412848, 0, 0, 0] := by
  decide +kernel

theorem rows2494 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2494 = true := by
  decide +kernel

theorem tot2494 : totK PD2M8K2 D2M8K2.t2494 = [166033326510, 404790855933, 263859044974, 66190072274, 2814597007, 0, 0, 0] := by
  decide +kernel

theorem rows2495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2495 = true := by
  decide +kernel

theorem tot2495 : totK PD2M8K2 D2M8K2.t2495 = [183430272755, 457569541117, 253725454679, 19949575071, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
