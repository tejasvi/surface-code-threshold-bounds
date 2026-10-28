import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16108 = true := by
  decide +kernel

theorem tot16108 : totK PD2M8K2 D2M8K2.t16108 = [0, 0, 209302555506, 480693017906, 182776620006, 7430810494, 0, 0] := by
  decide +kernel

theorem rows16109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16109 = true := by
  decide +kernel

theorem tot16109 : totK PD2M8K2 D2M8K2.t16109 = [0, 0, 150519354518, 434111559853, 298563759993, 33295318351, 0, 0] := by
  decide +kernel

theorem rows16110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16110 = true := by
  decide +kernel

theorem tot16110 : totK PD2M8K2 D2M8K2.t16110 = [0, 0, 194484341129, 471775039708, 231792057328, 14704281365, 0, 0] := by
  decide +kernel

theorem rows16111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16111 = true := by
  decide +kernel

theorem tot16111 : totK PD2M8K2 D2M8K2.t16111 = [0, 0, 150759416815, 459970979153, 285724594877, 26062423346, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
