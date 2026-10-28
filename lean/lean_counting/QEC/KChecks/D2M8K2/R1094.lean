import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4376 = true := by
  decide +kernel

theorem tot4376 : totK PD2M8K2 D2M8K2.t4376 = [0, 90236764506, 359754352309, 363996693694, 68321555340, 1096505104, 0, 0] := by
  decide +kernel

theorem rows4377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4377 = true := by
  decide +kernel

theorem tot4377 : totK PD2M8K2 D2M8K2.t4377 = [0, 0, 272747154059, 522611061913, 101248696764, 1069412848, 0, 0] := by
  decide +kernel

theorem rows4378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4378 = true := by
  decide +kernel

theorem tot4378 : totK PD2M8K2 D2M8K2.t4378 = [0, 190823817406, 456560295719, 224090922132, 34341867753, 2814597007, 0, 0] := by
  decide +kernel

theorem rows4379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4379 = true := by
  decide +kernel

theorem tot4379 : totK PD2M8K2 D2M8K2.t4379 = [0, 212528475952, 475027881200, 212233044473, 12736340443, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
