import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13272 = true := by
  decide +kernel

theorem tot13272 : totK PD2M8K2 D2M8K2.t13272 = [0, 0, 160195502442, 442738998149, 279830766395, 27943120115, 0, 0] := by
  decide +kernel

theorem rows13273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13273 = true := by
  decide +kernel

theorem tot13273 : totK PD2M8K2 D2M8K2.t13273 = [0, 0, 190461802742, 472427918648, 217937810165, 12320791933, 0, 0] := by
  decide +kernel

theorem rows13274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13274 = true := by
  decide +kernel

theorem tot13274 : totK PD2M8K2 D2M8K2.t13274 = [0, 0, 58238641821, 400912012607, 400581942591, 41979228303, 0, 0] := by
  decide +kernel

theorem rows13275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13275 = true := by
  decide +kernel

theorem tot13275 : totK PD2M8K2 D2M8K2.t13275 = [0, 0, 52710268747, 251859772352, 425576230152, 136960067123, 5159868635, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
