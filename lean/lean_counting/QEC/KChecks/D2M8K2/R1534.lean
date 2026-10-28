import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6136 = true := by
  decide +kernel

theorem tot6136 : totK PD2M8K2 D2M8K2.t6136 = [90838862230, 373432906574, 356698479181, 58545417265, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows6137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6137 = true := by
  decide +kernel

theorem tot6137 : totK PD2M8K2 D2M8K2.t6137 = [0, 317791200290, 504612800135, 79798933160, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6138 = true := by
  decide +kernel

theorem tot6138 : totK PD2M8K2 D2M8K2.t6138 = [157159411878, 385465221761, 273814599266, 84807446895, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows6139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6139 = true := by
  decide +kernel

theorem tot6139 : totK PD2M8K2 D2M8K2.t6139 = [164235945308, 439842708451, 261804265791, 22558126148, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
