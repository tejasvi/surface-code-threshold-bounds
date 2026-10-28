import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14244 = true := by
  decide +kernel

theorem tot14244 : totK PD2M8K2 D2M8K2.t14244 = [0, 215656851303, 490190091980, 176969634808, 5253830308, 0, 0, 0] := by
  decide +kernel

theorem rows14245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14245 = true := by
  decide +kernel

theorem tot14245 : totK PD2M8K2 D2M8K2.t14245 = [0, 191664684142, 450182882545, 210189260738, 16891742343, 0, 0, 0] := by
  decide +kernel

theorem rows14246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14246 = true := by
  decide +kernel

theorem tot14246 : totK PD2M8K2 D2M8K2.t14246 = [0, 91708558453, 387758268892, 316715112264, 51634312787, 1138244013, 0, 0] := by
  decide +kernel

theorem rows14247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14247 = true := by
  decide +kernel

theorem tot14247 : totK PD2M8K2 D2M8K2.t14247 = [0, 58841614274, 385835438190, 391338728905, 41211974721, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
