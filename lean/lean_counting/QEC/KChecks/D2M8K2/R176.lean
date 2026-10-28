import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t704 = true := by
  decide +kernel

theorem tot704 : totK PD2M8K2 D2M8K2.t704 = [85741851239, 324182554984, 375896877240, 101767525748, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t705 = true := by
  decide +kernel

theorem tot705 : totK PD2M8K2 D2M8K2.t705 = [169071665521, 445032788616, 261029810283, 27132277527, 0, 0, 0, 0] := by
  decide +kernel

theorem rows706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t706 = true := by
  decide +kernel

theorem tot706 : totK PD2M8K2 D2M8K2.t706 = [181015165609, 485521558950, 233085564316, 12169895203, 0, 0, 0, 0] := by
  decide +kernel

theorem rows707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t707 = true := by
  decide +kernel

theorem tot707 : totK PD2M8K2 D2M8K2.t707 = [0, 276383389340, 512311631852, 100606351565, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
