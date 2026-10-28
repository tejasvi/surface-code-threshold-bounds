import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11292 = true := by
  decide +kernel

theorem tot11292 : totK PD2M8K2 D2M8K2.t11292 = [93574619190, 383552344664, 394869309034, 54905677080, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11293 = true := by
  decide +kernel

theorem tot11293 : totK PD2M8K2 D2M8K2.t11293 = [175593870761, 451756988658, 264436071878, 21387845861, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11294 = true := by
  decide +kernel

theorem tot11294 : totK PD2M8K2 D2M8K2.t11294 = [159791897586, 453402217815, 265929673158, 25288999518, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11295 = true := by
  decide +kernel

theorem tot11295 : totK PD2M8K2 D2M8K2.t11295 = [0, 179516633393, 443349141198, 256943448784, 25364689049, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
