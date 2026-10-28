import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3440 = true := by
  decide +kernel

theorem tot3440 : totK PD2M8K2 D2M8K2.t3440 = [177860025660, 449149526111, 264081029730, 23601986982, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3441 = true := by
  decide +kernel

theorem tot3441 : totK PD2M8K2 D2M8K2.t3441 = [80563057922, 362266799306, 370908403900, 72440255304, 1197396724, 0, 0, 0] := by
  decide +kernel

theorem rows3442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3442 = true := by
  decide +kernel

theorem tot3442 : totK PD2M8K2 D2M8K2.t3442 = [0, 246720276017, 493450749742, 154887391264, 8464368736, 0, 0, 0] := by
  decide +kernel

theorem rows3443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3443 = true := by
  decide +kernel

theorem tot3443 : totK PD2M8K2 D2M8K2.t3443 = [144445137846, 361045160606, 291486280789, 85485184026, 3575904516, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
