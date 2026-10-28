import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11476 = true := by
  decide +kernel

theorem tot11476 : totK PD2M8K2 D2M8K2.t11476 = [0, 186768092506, 450783393945, 252796979720, 29189528148, 0, 0, 0] := by
  decide +kernel

theorem rows11477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11477 = true := by
  decide +kernel

theorem tot11477 : totK PD2M8K2 D2M8K2.t11477 = [0, 106005114803, 419080511036, 330199590204, 32202070855, 0, 0, 0] := by
  decide +kernel

theorem rows11478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11478 = true := by
  decide +kernel

theorem tot11478 : totK PD2M8K2 D2M8K2.t11478 = [0, 0, 295442544080, 512027071779, 100804240513, 1096505104, 0, 0] := by
  decide +kernel

theorem rows11479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11479 = true := by
  decide +kernel

theorem tot11479 : totK PD2M8K2 D2M8K2.t11479 = [0, 153057018287, 379200711017, 274656323973, 89492766876, 3884009855, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
