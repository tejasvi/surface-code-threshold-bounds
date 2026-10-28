import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12968 = true := by
  decide +kernel

theorem tot12968 : totK PD2M8K2 D2M8K2.t12968 = [0, 0, 296064131372, 517699173179, 99180430349, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12969 = true := by
  decide +kernel

theorem tot12969 : totK PD2M8K2 D2M8K2.t12969 = [0, 171051348884, 377336760465, 247248514582, 81346263526, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12970 = true := by
  decide +kernel

theorem tot12970 : totK PD2M8K2 D2M8K2.t12970 = [0, 141346995878, 429185650119, 302668281352, 30978013238, 0, 0, 0] := by
  decide +kernel

theorem rows12971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12971 = true := by
  decide +kernel

theorem tot12971 : totK PD2M8K2 D2M8K2.t12971 = [0, 91557279539, 343258299830, 366679207550, 77632646870, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
