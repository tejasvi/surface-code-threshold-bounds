import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12272 = true := by
  decide +kernel

theorem tot12272 : totK PD2M8K2 D2M8K2.t12272 = [0, 47395290273, 353817632312, 397000528728, 60657913037, 1021600638, 0, 0] := by
  decide +kernel

theorem rows12273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12273 = true := by
  decide +kernel

theorem tot12273 : totK PD2M8K2 D2M8K2.t12273 = [0, 62305036801, 309068002348, 382929270822, 91918588940, 3552795014, 0, 0] := by
  decide +kernel

theorem rows12274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12274 = true := by
  decide +kernel

theorem tot12274 : totK PD2M8K2 D2M8K2.t12274 = [0, 189608546192, 455479296359, 240761657109, 20679269382, 0, 0, 0] := by
  decide +kernel

theorem rows12275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12275 = true := by
  decide +kernel

theorem tot12275 : totK PD2M8K2 D2M8K2.t12275 = [90010399694, 257646918219, 339231547028, 194852530322, 16916338109, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
