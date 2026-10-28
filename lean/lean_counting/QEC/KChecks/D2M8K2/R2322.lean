import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9288 = true := by
  decide +kernel

theorem tot9288 : totK PD2M8K2 D2M8K2.t9288 = [108294820813, 328711762993, 321809134057, 144947278374, 13444587001, 0, 0, 0] := by
  decide +kernel

theorem rows9289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9289 = true := by
  decide +kernel

theorem tot9289 : totK PD2M8K2 D2M8K2.t9289 = [180602925376, 451116694783, 232966508057, 17115888737, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9290 = true := by
  decide +kernel

theorem tot9290 : totK PD2M8K2 D2M8K2.t9290 = [123535522706, 425707893631, 299542337309, 28297393084, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9291 = true := by
  decide +kernel

theorem tot9291 : totK PD2M8K2 D2M8K2.t9291 = [0, 271845605565, 502776471605, 111279681724, 1369150432, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
