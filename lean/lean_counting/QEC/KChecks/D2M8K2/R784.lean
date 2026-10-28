import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3136 = true := by
  decide +kernel

theorem tot3136 : totK PD2M8K2 D2M8K2.t3136 = [0, 232064857174, 484026527624, 166398290908, 9473607896, 0, 0, 0] := by
  decide +kernel

theorem rows3137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3137 = true := by
  decide +kernel

theorem tot3137 : totK PD2M8K2 D2M8K2.t3137 = [154825709772, 400612246614, 277691788409, 62972990673, 2566665356, 0, 0, 0] := by
  decide +kernel

theorem rows3138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3138 = true := by
  decide +kernel

theorem tot3138 : totK PD2M8K2 D2M8K2.t3138 = [166090603985, 438940774968, 275695479469, 30303442194, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3139 = true := by
  decide +kernel

theorem tot3139 : totK PD2M8K2 D2M8K2.t3139 = [90952881055, 368940141026, 350306686883, 64242978593, 1096156699, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
