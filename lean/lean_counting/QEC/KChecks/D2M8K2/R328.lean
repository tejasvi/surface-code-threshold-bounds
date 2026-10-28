import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1312 = true := by
  decide +kernel

theorem tot1312 : totK PD2M8K2 D2M8K2.t1312 = [0, 191835728942, 442895762400, 245958523617, 23251052789, 0, 0, 0] := by
  decide +kernel

theorem rows1313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1313 = true := by
  decide +kernel

theorem tot1313 : totK PD2M8K2 D2M8K2.t1313 = [51427959908, 191279394164, 399059242338, 251136014923, 22079952194, 0, 0, 0] := by
  decide +kernel

theorem rows1314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1314 = true := by
  decide +kernel

theorem tot1314 : totK PD2M8K2 D2M8K2.t1314 = [188444461767, 484548033826, 210646644403, 9819557711, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1315 = true := by
  decide +kernel

theorem tot1315 : totK PD2M8K2 D2M8K2.t1315 = [174498163380, 468105043459, 240093253768, 13751672343, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
