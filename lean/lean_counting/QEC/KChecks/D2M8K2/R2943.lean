import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11772 = true := by
  decide +kernel

theorem tot11772 : totK PD2M8K2 D2M8K2.t11772 = [0, 193700734506, 459992890905, 243382059861, 23353932091, 0, 0, 0] := by
  decide +kernel

theorem rows11773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11773 = true := by
  decide +kernel

theorem tot11773 : totK PD2M8K2 D2M8K2.t11773 = [0, 188754742390, 476091623344, 222527743788, 15849299976, 0, 0, 0] := by
  decide +kernel

theorem rows11774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11774 = true := by
  decide +kernel

theorem tot11774 : totK PD2M8K2 D2M8K2.t11774 = [0, 0, 361512048848, 485667059450, 59474132060, 0, 0, 0] := by
  decide +kernel

theorem rows11775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11775 = true := by
  decide +kernel

theorem tot11775 : totK PD2M8K2 D2M8K2.t11775 = [0, 90893841501, 326642890878, 376940031183, 102258100016, 3880716147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
