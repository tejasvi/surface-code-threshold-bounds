import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9988 = true := by
  decide +kernel

theorem tot9988 : totK PD2M8K2 D2M8K2.t9988 = [0, 0, 0, 269068478315, 513841914876, 101021429963, 1369150432, 0] := by
  decide +kernel

theorem rows9989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9989 = true := by
  decide +kernel

theorem tot9989 : totK PD2M8K2 D2M8K2.t9989 = [0, 0, 138449963357, 419754642198, 326432227548, 33385077108, 0, 0] := by
  decide +kernel

theorem rows9990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9990 = true := by
  decide +kernel

theorem tot9990 : totK PD2M8K2 D2M8K2.t9990 = [0, 0, 189980759500, 471141035051, 224697431974, 13207056824, 0, 0] := by
  decide +kernel

theorem rows9991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9991 = true := by
  decide +kernel

theorem tot9991 : totK PD2M8K2 D2M8K2.t9991 = [0, 0, 0, 387029139944, 470595302666, 52250943143, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
