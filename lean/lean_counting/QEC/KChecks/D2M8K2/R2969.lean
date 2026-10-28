import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11876 = true := by
  decide +kernel

theorem tot11876 : totK PD2M8K2 D2M8K2.t11876 = [90840904916, 359633798876, 367656452416, 67101242570, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows11877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11877 = true := by
  decide +kernel

theorem tot11877 : totK PD2M8K2 D2M8K2.t11877 = [0, 316677729908, 510180958436, 81482726815, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11878 = true := by
  decide +kernel

theorem tot11878 : totK PD2M8K2 D2M8K2.t11878 = [158854370654, 389335019779, 261849977051, 81828412134, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows11879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11879 = true := by
  decide +kernel

theorem tot11879 : totK PD2M8K2 D2M8K2.t11879 = [200692535381, 449872308334, 221151043024, 17007459867, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
