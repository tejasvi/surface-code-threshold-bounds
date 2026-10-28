import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t468 = true := by
  decide +kernel

theorem tot468 : totK PD2M8K2 D2M8K2.t468 = [0, 0, 284855724860, 509558598210, 90953956702, 1096505104, 0, 0] := by
  decide +kernel

theorem rows469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t469 = true := by
  decide +kernel

theorem tot469 : totK PD2M8K2 D2M8K2.t469 = [0, 91675999226, 339330971320, 360255765525, 91800233726, 3820764243, 0, 0] := by
  decide +kernel

theorem rows470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t470 = true := by
  decide +kernel

theorem tot470 : totK PD2M8K2 D2M8K2.t470 = [0, 182459923671, 443222055568, 251131024577, 25437706687, 0, 0, 0] := by
  decide +kernel

theorem rows471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t471 = true := by
  decide +kernel

theorem tot471 : totK PD2M8K2 D2M8K2.t471 = [0, 140271011081, 443642090718, 303302147533, 21962056034, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
