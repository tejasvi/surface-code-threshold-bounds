import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9700 = true := by
  decide +kernel

theorem tot9700 : totK PD2M8K2 D2M8K2.t9700 = [0, 175067059040, 382947785066, 244850047659, 98929401674, 6779302614, 0, 0] := by
  decide +kernel

theorem rows9701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9701 = true := by
  decide +kernel

theorem tot9701 : totK PD2M8K2 D2M8K2.t9701 = [0, 161767817459, 444430786365, 286381258329, 30002234705, 0, 0, 0] := by
  decide +kernel

theorem rows9702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9702 = true := by
  decide +kernel

theorem tot9702 : totK PD2M8K2 D2M8K2.t9702 = [0, 100160278937, 423974178834, 342974652911, 34156375343, 0, 0, 0] := by
  decide +kernel

theorem rows9703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9703 = true := by
  decide +kernel

theorem tot9703 : totK PD2M8K2 D2M8K2.t9703 = [0, 0, 216175809502, 481423063979, 184846813613, 9668735432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
