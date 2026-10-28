import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5376 = true := by
  decide +kernel

theorem tot5376 : totK PD2M8K2 D2M8K2.t5376 = [0, 0, 82431197077, 358359796258, 381083419544, 68027573001, 1107157161, 0] := by
  decide +kernel

theorem rows5377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5377 = true := by
  decide +kernel

theorem tot5377 : totK PD2M8K2 D2M8K2.t5377 = [0, 0, 18514691823, 287676388256, 456117161769, 110331330265, 3824247485, 0] := by
  decide +kernel

theorem rows5378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5378 = true := by
  decide +kernel

theorem tot5378 : totK PD2M8K2 D2M8K2.t5378 = [0, 0, 189418753873, 463569873381, 239681186459, 20128547347, 0, 0] := by
  decide +kernel

theorem rows5379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5379 = true := by
  decide +kernel

theorem tot5379 : totK PD2M8K2 D2M8K2.t5379 = [0, 0, 184417792611, 475042237947, 237004353210, 12551143345, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
