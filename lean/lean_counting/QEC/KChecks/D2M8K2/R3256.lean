import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13024 = true := by
  decide +kernel

theorem tot13024 : totK PD2M8K2 D2M8K2.t13024 = [0, 161764526861, 460666027375, 249399353762, 13183854691, 0, 0, 0] := by
  decide +kernel

theorem rows13025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13025 = true := by
  decide +kernel

theorem tot13025 : totK PD2M8K2 D2M8K2.t13025 = [0, 0, 277067983388, 502810413300, 107561663166, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13026 = true := by
  decide +kernel

theorem tot13026 : totK PD2M8K2 D2M8K2.t13026 = [0, 100016994609, 378043200621, 390810019071, 49599131374, 0, 0, 0] := by
  decide +kernel

theorem rows13027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13027 = true := by
  decide +kernel

theorem tot13027 : totK PD2M8K2 D2M8K2.t13027 = [0, 198528747426, 478264758658, 225531540693, 14035003879, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
