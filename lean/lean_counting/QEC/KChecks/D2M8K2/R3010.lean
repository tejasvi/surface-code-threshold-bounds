import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12040 = true := by
  decide +kernel

theorem tot12040 : totK PD2M8K2 D2M8K2.t12040 = [0, 68412647006, 342935611247, 395856642748, 73580190943, 1164319620, 0, 0] := by
  decide +kernel

theorem rows12041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12041 = true := by
  decide +kernel

theorem tot12041 : totK PD2M8K2 D2M8K2.t12041 = [0, 87718631415, 394300138163, 373601494918, 41208301100, 0, 0, 0] := by
  decide +kernel

theorem rows12042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12042 = true := by
  decide +kernel

theorem tot12042 : totK PD2M8K2 D2M8K2.t12042 = [0, 179044929304, 439858848178, 264949506381, 26454652327, 0, 0, 0] := by
  decide +kernel

theorem rows12043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12043 = true := by
  decide +kernel

theorem tot12043 : totK PD2M8K2 D2M8K2.t12043 = [0, 155917868574, 453522135559, 258994163938, 16796403474, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
