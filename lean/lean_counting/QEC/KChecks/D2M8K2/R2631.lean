import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10524 = true := by
  decide +kernel

theorem tot10524 : totK PD2M8K2 D2M8K2.t10524 = [0, 0, 221741666207, 492709740137, 193183550690, 5516070556, 0, 0] := by
  decide +kernel

theorem rows10525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10525 = true := by
  decide +kernel

theorem tot10525 : totK PD2M8K2 D2M8K2.t10525 = [0, 0, 187196213076, 470028811708, 214542812437, 12319708528, 0, 0] := by
  decide +kernel

theorem rows10526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10526 = true := by
  decide +kernel

theorem tot10526 : totK PD2M8K2 D2M8K2.t10526 = [0, 0, 158693442072, 485504131432, 234694585892, 10178307621, 0, 0] := by
  decide +kernel

theorem rows10527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10527 = true := by
  decide +kernel

theorem tot10527 : totK PD2M8K2 D2M8K2.t10527 = [0, 0, 177150244171, 430707273177, 230503003623, 18264884893, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
