import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8776 = true := by
  decide +kernel

theorem tot8776 : totK PD2M8K2 D2M8K2.t8776 = [0, 42421295341, 217229546032, 430651352875, 202528418415, 8100177866, 0, 0] := by
  decide +kernel

theorem rows8777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8777 = true := by
  decide +kernel

theorem tot8777 : totK PD2M8K2 D2M8K2.t8777 = [0, 198820009648, 452145668079, 238367094725, 23200982689, 0, 0, 0] := by
  decide +kernel

theorem rows8778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8778 = true := by
  decide +kernel

theorem tot8778 : totK PD2M8K2 D2M8K2.t8778 = [0, 142124878872, 468683106515, 266374327211, 14926124038, 0, 0, 0] := by
  decide +kernel

theorem rows8779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8779 = true := by
  decide +kernel

theorem tot8779 : totK PD2M8K2 D2M8K2.t8779 = [0, 0, 238792095317, 497036397260, 140698353733, 2309606161, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
