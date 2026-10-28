import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3076 = true := by
  decide +kernel

theorem tot3076 : totK PD2M8K2 D2M8K2.t3076 = [0, 0, 187689631584, 455539983726, 219377884832, 17854363044, 0, 0] := by
  decide +kernel

theorem rows3077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3077 = true := by
  decide +kernel

theorem tot3077 : totK PD2M8K2 D2M8K2.t3077 = [0, 0, 111775798334, 420820468914, 285579140374, 28860339638, 0, 0] := by
  decide +kernel

theorem rows3078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3078 = true := by
  decide +kernel

theorem tot3078 : totK PD2M8K2 D2M8K2.t3078 = [0, 0, 0, 325167582645, 448080827229, 70313994489, 0, 0] := by
  decide +kernel

theorem rows3079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3079 = true := by
  decide +kernel

theorem tot3079 : totK PD2M8K2 D2M8K2.t3079 = [0, 173180509234, 408332239585, 157671456737, 75470985126, 53225032577, 3718133097, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
