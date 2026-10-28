import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9264 = true := by
  decide +kernel

theorem tot9264 : totK PD2M8K2 D2M8K2.t9264 = [0, 237297861461, 486641826232, 165673391582, 9482920370, 0, 0, 0] := by
  decide +kernel

theorem rows9265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9265 = true := by
  decide +kernel

theorem tot9265 : totK PD2M8K2 D2M8K2.t9265 = [146186006935, 387962702135, 292502933594, 65052546610, 2569691499, 0, 0, 0] := by
  decide +kernel

theorem rows9266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9266 = true := by
  decide +kernel

theorem tot9266 : totK PD2M8K2 D2M8K2.t9266 = [178446354003, 436633991010, 264271768795, 30240056193, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9267 = true := by
  decide +kernel

theorem tot9267 : totK PD2M8K2 D2M8K2.t9267 = [95516023307, 423017489431, 342052700001, 33376744064, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
