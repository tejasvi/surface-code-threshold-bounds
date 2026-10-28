import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3064 = true := by
  decide +kernel

theorem tot3064 : totK PD2M8K2 D2M8K2.t3064 = [0, 170465635573, 446252228797, 261410176429, 20655089278, 0, 0, 0] := by
  decide +kernel

theorem rows3065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3065 = true := by
  decide +kernel

theorem tot3065 : totK PD2M8K2 D2M8K2.t3065 = [0, 92722701599, 365189155528, 356016042925, 71683673347, 1096505104, 0, 0] := by
  decide +kernel

theorem rows3066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3066 = true := by
  decide +kernel

theorem tot3066 : totK PD2M8K2 D2M8K2.t3066 = [0, 0, 309589937998, 513434098301, 87320765749, 1069412848, 0, 0] := by
  decide +kernel

theorem rows3067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3067 = true := by
  decide +kernel

theorem tot3067 : totK PD2M8K2 D2M8K2.t3067 = [0, 0, 171549772232, 478712642863, 204706813146, 10093459964, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
