import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16300 = true := by
  decide +kernel

theorem tot16300 : totK PD2M8K2 D2M8K2.t16300 = [0, 0, 205726542447, 476938083586, 221225818434, 13591980714, 0, 0] := by
  decide +kernel

theorem rows16301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16301 = true := by
  decide +kernel

theorem tot16301 : totK PD2M8K2 D2M8K2.t16301 = [0, 0, 44497231905, 314499718640, 429998776366, 98894638054, 1268739303, 0] := by
  decide +kernel

theorem rows16302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16302 = true := by
  decide +kernel

theorem tot16302 : totK PD2M8K2 D2M8K2.t16302 = [0, 0, 0, 218578734881, 484522848338, 175960441736, 7373134680, 0] := by
  decide +kernel

theorem rows16303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16303 = true := by
  decide +kernel

theorem tot16303 : totK PD2M8K2 D2M8K2.t16303 = [0, 0, 0, 182223138208, 470320322278, 215152711146, 14704558535, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
