import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11656 = true := by
  decide +kernel

theorem tot11656 : totK PD2M8K2 D2M8K2.t11656 = [0, 175591062921, 466167726133, 239283869905, 20354185925, 0, 0, 0] := by
  decide +kernel

theorem rows11657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11657 = true := by
  decide +kernel

theorem tot11657 : totK PD2M8K2 D2M8K2.t11657 = [0, 180100867441, 458149209671, 254379647154, 16627933934, 0, 0, 0] := by
  decide +kernel

theorem rows11658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11658 = true := by
  decide +kernel

theorem tot11658 : totK PD2M8K2 D2M8K2.t11658 = [0, 87927492280, 370538993738, 346349423977, 64364225376, 1162935789, 0, 0] := by
  decide +kernel

theorem rows11659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11659 = true := by
  decide +kernel

theorem tot11659 : totK PD2M8K2 D2M8K2.t11659 = [0, 0, 261723787532, 464905610681, 145357185180, 8416438934, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
