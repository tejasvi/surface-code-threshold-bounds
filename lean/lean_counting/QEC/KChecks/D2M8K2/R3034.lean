import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12136 = true := by
  decide +kernel

theorem tot12136 : totK PD2M8K2 D2M8K2.t12136 = [0, 170758542240, 438252926542, 273753036868, 29719848591, 0, 0, 0] := by
  decide +kernel

theorem rows12137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12137 = true := by
  decide +kernel

theorem tot12137 : totK PD2M8K2 D2M8K2.t12137 = [0, 174590559317, 479607776378, 249852966779, 13916467904, 0, 0, 0] := by
  decide +kernel

theorem rows12138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12138 = true := by
  decide +kernel

theorem tot12138 : totK PD2M8K2 D2M8K2.t12138 = [0, 0, 287447955840, 513617971466, 98690432122, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12139 = true := by
  decide +kernel

theorem tot12139 : totK PD2M8K2 D2M8K2.t12139 = [0, 0, 212549656755, 495971838952, 172166489137, 5253830308, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
