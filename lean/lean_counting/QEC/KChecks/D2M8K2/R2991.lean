import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11964 = true := by
  decide +kernel

theorem tot11964 : totK PD2M8K2 D2M8K2.t11964 = [0, 83641152863, 308751519267, 356343115236, 106968427207, 4923312241, 0, 0] := by
  decide +kernel

theorem rows11965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11965 = true := by
  decide +kernel

theorem tot11965 : totK PD2M8K2 D2M8K2.t11965 = [0, 154795865204, 465868119324, 255526535449, 14539407580, 0, 0, 0] := by
  decide +kernel

theorem rows11966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11966 = true := by
  decide +kernel

theorem tot11966 : totK PD2M8K2 D2M8K2.t11966 = [0, 176102677452, 475892405891, 240816527128, 13888635665, 0, 0, 0] := by
  decide +kernel

theorem rows11967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11967 = true := by
  decide +kernel

theorem tot11967 : totK PD2M8K2 D2M8K2.t11967 = [0, 0, 303280975172, 471485760865, 79389577013, 1053411165, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
