import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12548 = true := by
  decide +kernel

theorem tot12548 : totK PD2M8K2 D2M8K2.t12548 = [0, 0, 323807716567, 513490986655, 81097596896, 0, 0, 0] := by
  decide +kernel

theorem rows12549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12549 = true := by
  decide +kernel

theorem tot12549 : totK PD2M8K2 D2M8K2.t12549 = [0, 151806946431, 377949961240, 277273946809, 86019340584, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12550 = true := by
  decide +kernel

theorem tot12550 : totK PD2M8K2 D2M8K2.t12550 = [0, 200679944091, 453177436374, 225464743674, 17178404490, 0, 0, 0] := by
  decide +kernel

theorem rows12551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12551 = true := by
  decide +kernel

theorem tot12551 : totK PD2M8K2 D2M8K2.t12551 = [0, 30722815107, 306131037754, 448710506784, 103761677605, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
