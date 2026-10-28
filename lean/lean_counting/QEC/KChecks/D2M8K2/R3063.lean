import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12252 = true := by
  decide +kernel

theorem tot12252 : totK PD2M8K2 D2M8K2.t12252 = [52761177660, 235489776702, 419487568511, 166663826502, 10740121073, 0, 0, 0] := by
  decide +kernel

theorem rows12253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12253 = true := by
  decide +kernel

theorem tot12253 : totK PD2M8K2 D2M8K2.t12253 = [175212677081, 457081212010, 256537546379, 23144534348, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12254 = true := by
  decide +kernel

theorem tot12254 : totK PD2M8K2 D2M8K2.t12254 = [196858023842, 461882213452, 227726624523, 17094477172, 0, 0, 0, 0] := by
  decide +kernel

theorem rows12255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12255 = true := by
  decide +kernel

theorem tot12255 : totK PD2M8K2 D2M8K2.t12255 = [0, 312010445029, 486620808415, 90493365569, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
