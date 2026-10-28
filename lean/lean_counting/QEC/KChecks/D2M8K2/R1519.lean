import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6076 = true := by
  decide +kernel

theorem tot6076 : totK PD2M8K2 D2M8K2.t6076 = [0, 0, 264518354978, 496783380549, 127873283353, 3884009855, 0, 0] := by
  decide +kernel

theorem rows6077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6077 = true := by
  decide +kernel

theorem tot6077 : totK PD2M8K2 D2M8K2.t6077 = [0, 0, 176417715816, 496730851927, 182163383182, 3708492342, 0, 0] := by
  decide +kernel

theorem rows6078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6078 = true := by
  decide +kernel

theorem tot6078 : totK PD2M8K2 D2M8K2.t6078 = [0, 0, 180223196545, 467613173625, 238170192075, 19841673311, 0, 0] := by
  decide +kernel

theorem rows6079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6079 = true := by
  decide +kernel

theorem tot6079 : totK PD2M8K2 D2M8K2.t6079 = [0, 0, 195004821498, 462705897477, 209863706754, 16259028532, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
