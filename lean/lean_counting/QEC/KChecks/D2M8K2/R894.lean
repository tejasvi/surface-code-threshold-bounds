import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3576 = true := by
  decide +kernel

theorem tot3576 : totK PD2M8K2 D2M8K2.t3576 = [0, 173885334915, 454857126097, 235324463265, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows3577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3577 = true := by
  decide +kernel

theorem tot3577 : totK PD2M8K2 D2M8K2.t3577 = [0, 83498587768, 385805239956, 351331481170, 62831767797, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3578 = true := by
  decide +kernel

theorem tot3578 : totK PD2M8K2 D2M8K2.t3578 = [0, 0, 300623767629, 510343275737, 81144461969, 0, 0, 0] := by
  decide +kernel

theorem rows3579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3579 = true := by
  decide +kernel

theorem tot3579 : totK PD2M8K2 D2M8K2.t3579 = [0, 180339226645, 453543137193, 253440643882, 22322454778, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
