import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7032 = true := by
  decide +kernel

theorem tot7032 : totK PD2M8K2 D2M8K2.t7032 = [0, 0, 193940426344, 470874596391, 209961883957, 14707859566, 0, 0] := by
  decide +kernel

theorem rows7033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7033 = true := by
  decide +kernel

theorem tot7033 : totK PD2M8K2 D2M8K2.t7033 = [0, 0, 164187019651, 462729668195, 205660327249, 8951135403, 0, 0] := by
  decide +kernel

theorem rows7034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7034 = true := by
  decide +kernel

theorem tot7034 : totK PD2M8K2 D2M8K2.t7034 = [0, 0, 89045695041, 348365945173, 361697104995, 74044745701, 1288491354, 0] := by
  decide +kernel

theorem rows7035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7035 = true := by
  decide +kernel

theorem tot7035 : totK PD2M8K2 D2M8K2.t7035 = [0, 0, 30760524954, 340114059654, 454102299014, 45029648728, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
