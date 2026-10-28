import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12440 = true := by
  decide +kernel

theorem tot12440 : totK PD2M8K2 D2M8K2.t12440 = [0, 0, 214235439418, 500807324059, 184189096103, 5393550755, 0, 0] := by
  decide +kernel

theorem rows12441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12441 = true := by
  decide +kernel

theorem tot12441 : totK PD2M8K2 D2M8K2.t12441 = [0, 171550951199, 445041986228, 265752322360, 25600882052, 0, 0, 0] := by
  decide +kernel

theorem rows12442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12442 = true := by
  decide +kernel

theorem tot12442 : totK PD2M8K2 D2M8K2.t12442 = [0, 180389826693, 473908163914, 234857993030, 14484397502, 0, 0, 0] := by
  decide +kernel

theorem rows12443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12443 = true := by
  decide +kernel

theorem tot12443 : totK PD2M8K2 D2M8K2.t12443 = [0, 67264054882, 325360650995, 405862874066, 79733712736, 1128973710, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
