import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14512 = true := by
  decide +kernel

theorem tot14512 : totK PD2M8K2 D2M8K2.t14512 = [173576550852, 396078831436, 248667191954, 77598291228, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows14513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14513 = true := by
  decide +kernel

theorem tot14513 : totK PD2M8K2 D2M8K2.t14513 = [158195872060, 449755268853, 284704930650, 27323801875, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14514 = true := by
  decide +kernel

theorem tot14514 : totK PD2M8K2 D2M8K2.t14514 = [92620862180, 355744833925, 371979185527, 74183044016, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows14515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14515 = true := by
  decide +kernel

theorem tot14515 : totK PD2M8K2 D2M8K2.t14515 = [0, 245382178811, 496300632622, 155192715361, 3680483203, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
