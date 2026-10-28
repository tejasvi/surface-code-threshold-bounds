import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14140 = true := by
  decide +kernel

theorem tot14140 : totK PD2M8K2 D2M8K2.t14140 = [0, 203468830445, 489658887117, 193621906246, 9610913563, 0, 0, 0] := by
  decide +kernel

theorem rows14141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14141 = true := by
  decide +kernel

theorem tot14141 : totK PD2M8K2 D2M8K2.t14141 = [0, 187514494661, 453660064935, 202915019450, 12206147664, 0, 0, 0] := by
  decide +kernel

theorem rows14142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14142 = true := by
  decide +kernel

theorem tot14142 : totK PD2M8K2 D2M8K2.t14142 = [0, 36932443061, 313504972090, 419017680156, 96722068960, 1369150432, 0, 0] := by
  decide +kernel

theorem rows14143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14143 = true := by
  decide +kernel

theorem tot14143 : totK PD2M8K2 D2M8K2.t14143 = [0, 87307959298, 376955364840, 356550883315, 45946403621, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
