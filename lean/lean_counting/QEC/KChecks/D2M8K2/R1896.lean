import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7584 = true := by
  decide +kernel

theorem tot7584 : totK PD2M8K2 D2M8K2.t7584 = [0, 0, 276836794000, 494061273426, 108860637833, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7585 = true := by
  decide +kernel

theorem tot7585 : totK PD2M8K2 D2M8K2.t7585 = [0, 92923763202, 379884509533, 390177009449, 49631273580, 0, 0, 0] := by
  decide +kernel

theorem rows7586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7586 = true := by
  decide +kernel

theorem tot7586 : totK PD2M8K2 D2M8K2.t7586 = [0, 166085142673, 445292904851, 267178870742, 21590722393, 0, 0, 0] := by
  decide +kernel

theorem rows7587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7587 = true := by
  decide +kernel

theorem tot7587 : totK PD2M8K2 D2M8K2.t7587 = [0, 158455256144, 456474289192, 277456279032, 29518671867, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
