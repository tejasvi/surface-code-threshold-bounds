import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7528 = true := by
  decide +kernel

theorem tot7528 : totK PD2M8K2 D2M8K2.t7528 = [0, 0, 196497999173, 472484347326, 229870705338, 11690219700, 0, 0] := by
  decide +kernel

theorem rows7529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7529 = true := by
  decide +kernel

theorem tot7529 : totK PD2M8K2 D2M8K2.t7529 = [0, 0, 107710533584, 437262413912, 334920391305, 34669323074, 0, 0] := by
  decide +kernel

theorem rows7530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7530 = true := by
  decide +kernel

theorem tot7530 : totK PD2M8K2 D2M8K2.t7530 = [0, 0, 0, 202737249666, 447559260669, 230541416044, 18850862804, 0] := by
  decide +kernel

theorem rows7531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7531 = true := by
  decide +kernel

theorem tot7531 : totK PD2M8K2 D2M8K2.t7531 = [0, 0, 66570406258, 243138501139, 410214045743, 160458155795, 5430859943, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
