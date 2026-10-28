import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11264 = true := by
  decide +kernel

theorem tot11264 : totK PD2M8K2 D2M8K2.t11264 = [101997513634, 418232596743, 337333180503, 33608612504, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11265 = true := by
  decide +kernel

theorem tot11265 : totK PD2M8K2 D2M8K2.t11265 = [0, 216642367949, 489352442622, 182275301213, 9587713104, 0, 0, 0] := by
  decide +kernel

theorem rows11266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11266 = true := by
  decide +kernel

theorem tot11266 : totK PD2M8K2 D2M8K2.t11266 = [77629098139, 329263572934, 367821503332, 94322296760, 3462014130, 0, 0, 0] := by
  decide +kernel

theorem rows11267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11267 = true := by
  decide +kernel

theorem tot11267 : totK PD2M8K2 D2M8K2.t11267 = [176782333843, 440982307388, 276354477839, 28914812675, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
