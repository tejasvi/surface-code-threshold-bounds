import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10304 = true := by
  decide +kernel

theorem tot10304 : totK PD2M8K2 D2M8K2.t10304 = [0, 166105465443, 433299311746, 276061747672, 30443446239, 0, 0, 0] := by
  decide +kernel

theorem rows10305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10305 = true := by
  decide +kernel

theorem tot10305 : totK PD2M8K2 D2M8K2.t10305 = [0, 158470454872, 472852981739, 267924591884, 14955112674, 0, 0, 0] := by
  decide +kernel

theorem rows10306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10306 = true := by
  decide +kernel

theorem tot10306 : totK PD2M8K2 D2M8K2.t10306 = [0, 0, 175093888648, 446639084068, 252241456689, 25116558953, 0, 0] := by
  decide +kernel

theorem rows10307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10307 = true := by
  decide +kernel

theorem tot10307 : totK PD2M8K2 D2M8K2.t10307 = [0, 0, 209064896280, 494824194234, 199779084928, 5430665091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
