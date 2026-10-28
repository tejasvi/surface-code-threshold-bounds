import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5556 = true := by
  decide +kernel

theorem tot5556 : totK PD2M8K2 D2M8K2.t5556 = [0, 293786264861, 494667357396, 109223622810, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows5557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5557 = true := by
  decide +kernel

theorem tot5557 : totK PD2M8K2 D2M8K2.t5557 = [0, 209197178655, 475112084133, 187128350337, 7439461435, 0, 0, 0] := by
  decide +kernel

theorem rows5558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5558 = true := by
  decide +kernel

theorem tot5558 : totK PD2M8K2 D2M8K2.t5558 = [0, 186961504857, 476311407225, 217212895931, 14704558535, 0, 0, 0] := by
  decide +kernel

theorem rows5559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5559 = true := by
  decide +kernel

theorem tot5559 : totK PD2M8K2 D2M8K2.t5559 = [0, 154061433896, 466416292077, 229413266176, 10735115630, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
