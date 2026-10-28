import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11564 = true := by
  decide +kernel

theorem tot11564 : totK PD2M8K2 D2M8K2.t11564 = [170926481118, 455954922697, 246879729485, 17334628918, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11565 = true := by
  decide +kernel

theorem tot11565 : totK PD2M8K2 D2M8K2.t11565 = [0, 238709792845, 512945345458, 142775405311, 2309606161, 0, 0, 0] := by
  decide +kernel

theorem rows11566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11566 = true := by
  decide +kernel

theorem tot11566 : totK PD2M8K2 D2M8K2.t11566 = [69288392984, 258707768131, 388114307330, 146232259596, 10740121073, 0, 0, 0] := by
  decide +kernel

theorem rows11567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11567 = true := by
  decide +kernel

theorem tot11567 : totK PD2M8K2 D2M8K2.t11567 = [187179937493, 484759447988, 216713269110, 9997409401, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
