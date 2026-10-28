import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7508 = true := by
  decide +kernel

theorem tot7508 : totK PD2M8K2 D2M8K2.t7508 = [0, 185774386049, 472470993668, 234609947467, 12749224408, 0, 0, 0] := by
  decide +kernel

theorem rows7509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7509 = true := by
  decide +kernel

theorem tot7509 : totK PD2M8K2 D2M8K2.t7509 = [0, 75067762744, 305999988158, 369771499028, 157541677668, 17186218589, 0, 0] := by
  decide +kernel

theorem rows7510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7510 = true := by
  decide +kernel

theorem tot7510 : totK PD2M8K2 D2M8K2.t7510 = [0, 0, 204850391747, 467929737449, 214501341846, 12208674056, 0, 0] := by
  decide +kernel

theorem rows7511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7511 = true := by
  decide +kernel

theorem tot7511 : totK PD2M8K2 D2M8K2.t7511 = [0, 53342041414, 225496597692, 419465459896, 197716422470, 8214505460, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
