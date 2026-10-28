import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t324 = true := by
  decide +kernel

theorem tot324 : totK PD2M8K2 D2M8K2.t324 = [194514098167, 456899046847, 241998750293, 23321274627, 0, 0, 0, 0] := by
  decide +kernel

theorem rows325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t325 = true := by
  decide +kernel

theorem tot325 : totK PD2M8K2 D2M8K2.t325 = [191123054367, 457628603542, 227043024113, 17019426241, 0, 0, 0, 0] := by
  decide +kernel

theorem rows326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t326 = true := by
  decide +kernel

theorem tot326 : totK PD2M8K2 D2M8K2.t326 = [0, 324980013610, 474804054982, 92688712848, 1096156699, 0, 0, 0] := by
  decide +kernel

theorem rows327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t327 = true := by
  decide +kernel

theorem tot327 : totK PD2M8K2 D2M8K2.t327 = [68041946609, 299640021593, 409937696631, 111151015269, 3880716147, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
