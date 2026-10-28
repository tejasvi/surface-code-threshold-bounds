import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8468 = true := by
  decide +kernel

theorem tot8468 : totK PD2M8K2 D2M8K2.t8468 = [0, 179781826033, 458357664692, 246011116314, 18185084111, 0, 0, 0] := by
  decide +kernel

theorem rows8469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8469 = true := by
  decide +kernel

theorem tot8469 : totK PD2M8K2 D2M8K2.t8469 = [0, 0, 308963369006, 497060526477, 90138003383, 1096505104, 0, 0] := by
  decide +kernel

theorem rows8470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8470 = true := by
  decide +kernel

theorem tot8470 : totK PD2M8K2 D2M8K2.t8470 = [0, 86831652183, 305041731490, 389533558039, 110125441293, 3884009855, 0, 0] := by
  decide +kernel

theorem rows8471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8471 = true := by
  decide +kernel

theorem tot8471 : totK PD2M8K2 D2M8K2.t8471 = [0, 168861611356, 477939455469, 222852518575, 10957502955, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
